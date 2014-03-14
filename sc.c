/* -*-mode: c; indent-tabs-mode: nil; c-basic-offset: 4; -*-  */
/*
 * This file is part of PuTTY SC, a modification of PuTTY
 * supporting smartcard for authentication.
 *
 * PuTTY SC is available at http://www.joebar.ch/puttysc/
 *
 * Copyright (C) 2005-2007 Pascal Buchbinder
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301, USA.
 *
 */

#ifdef DO_PKCS11_AUTH
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <assert.h>

/* putty */
#include "putty.h"
#include "ssh.h"
#include "pkcs11.h"

/* this */
#include "sc.h"

#ifndef FALSE
#define FALSE 0
#endif
#ifndef TRUE
#define TRUE 1
#endif

static const char rcsid_sc_c[] = "$Id: sc.c,v 1.34 2007/03/04 20:41:56 pbu Exp $";

/* this is the OID for rsaEncryption plus a required null object as the parameter field. */
/* for more on how ASN.1 works, see http://luca.ntop.org/Teaching/Appunti/asn1.html */

static const char OIDrsaEncryption[] = { 0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01, 0x05, 0x00 };
int find_substring( char * haystack, long haysize, const char* needle, long needlesize) ;
unsigned int asn1_length(unsigned char** cursor) ;
int extract_key_from_cert(unsigned char* cert, int certsize, unsigned char **expo, unsigned char** modu, 
			  int* elen, int* mlen);


#define SC_PUT_32BIT(cp, value) { \
        (cp)[0] = (unsigned char)((value) >> 24);       \
        (cp)[1] = (unsigned char)((value) >> 16);       \
        (cp)[2] = (unsigned char)((value) >> 8);        \
        (cp)[3] = (unsigned char)(value); }

static const u_char id_sha1[] = {
    0x30, 0x21, 0x30, 0x09,
    0x06, 0x05, 0x2b, 0x0e,
    0x03, 0x02, 0x1a, 0x05,
    0x00, 0x04, 0x14
};

#define SC_STR_MAX_LEN 8192
#define SC_MAX_O 20

void sc_write_syslog(char *msg) {
    char szSyslogBuffer[SC_STR_MAX_LEN];
    HANDLE  hEventLog;
    int rc;
    DWORD logw = 0x00000001L;
    
    sprintf(szSyslogBuffer, "%s: %s %s",
            "puttysc", "info", msg);
    
    if ((hEventLog = RegisterEventSource(NULL, "puttysc"))) {
        LPSTR aszStrings[] = {szSyslogBuffer};
        rc = ReportEvent(hEventLog,
                         (WORD)EVENTLOG_INFORMATION_TYPE,
                         0,
                         (DWORD)logw,
                         NULL,
                         1,
                         0,
                         (LPCTSTR*)aszStrings,
                         NULL);
        DeregisterEventSource(hEventLog);
    }
}

char *sc_base64key(char *data, int len) {
    int bi, bn;
    char out[4];
    int datalen = len;
    char *buffi = calloc(len + len, sizeof(char *));
    int buffi_pos = 0;
    for(bi=0;bi<(len + len); bi++) buffi[bi] = '\0';
    while (datalen > 0) {
        bn = (datalen < 3 ? datalen : 3);
        base64_encode_atom(data, bn, out);
        data += bn;
        datalen -= bn;
        for (bi = 0; bi < 4; bi++) {
            buffi[buffi_pos] = out[bi];
            buffi_pos++;
        }
    }
    return buffi;
}

void sc_free_sclib(sc_lib *sclib) {
    if(sclib->rsakey != NULL) {
        free(sclib->rsakey->exponent);
        free(sclib->rsakey->modulus);
        free(sclib->rsakey);
    }
    if (sclib->keystring != NULL) {
        free(sclib->keystring);
        sclib->keystring = NULL;
    }
    sclib->m_fl->C_Finalize(0);
    sclib->m_fl = 0;
    free(sclib->m_KeyID);
    sclib->m_KeyID = NULL;
    free(sclib->m_SshPK);
    sclib->m_SshPK = NULL;
    sclib->m_SshPK_len = 0;
    free(sclib->m_SshPk_alg);
    sclib->m_SshPk_alg = NULL;
    FreeLibrary(sclib->hLib);
    free(sclib);
}

int sc_init_library(void *f, int try_write_syslog, sc_lib *sclib,
                    Filename *pkcs11_libfile) {
    CK_FUNCTION_LIST_PTR fl  = 0;
    CK_C_GetFunctionList pGFL  = 0;
    unsigned long slot_count = 16;
    CK_SLOT_ID slots[16];
    CK_RV rv = 0;
    char *msg = "";

    memset(sclib, 0, sizeof(sc_lib));

    sclib->hLib = LoadLibrary(filename_to_str(pkcs11_libfile));

    if (sclib->hLib == NULL) {
        msg = "sc: Cannot load PKCS 11 DLL.";
        goto err;
    }
    pGFL= (CK_RV (*)(CK_FUNCTION_LIST_PTR_PTR))GetProcAddress(sclib->hLib, "C_GetFunctionList");
    if (pGFL == NULL) {
        msg = "sc: Cannot find GetFunctionList()";
        goto err;
    }
    rv = pGFL(&fl);
    if(rv != CKR_OK) {
        msg = "sc: Can't get function list";
        goto err;
    }
    rv = fl->C_Initialize (0); 
    if (CKR_OK != rv ) {
        msg = "sc: C_Initialize failed";
        goto err;
    }   
    rv = fl->C_GetSlotList (TRUE, slots, &slot_count);
    if (CKR_OK != rv) {
        msg = "sc: C_GetSlotList failed";
        goto err;
    }                       
    if (slot_count < 1) {
        msg = "sc: No token available";
        goto err;
    }
    sclib->m_fl = fl;
    return TRUE;
    
 err:
    logevent(f, msg);
    if(try_write_syslog) sc_write_syslog(msg);
    FreeLibrary(sclib->hLib);
    return FALSE;
}

/* In an attempt to work around the wierdness of the ActivClient
   library, I'm going to do an evil hack: If there's only one slot,
   I'm going to use it regardless of what the token_label is.
   ActivClient generates token labels on the fly, so we can't count on
   them being the same from one session to the next.  */

CK_SESSION_HANDLE sc_get_session(void *f, int try_write_syslog, CK_FUNCTION_LIST_PTR fl,
                                 const char *token_label) {
#define SC_MAX_SLOT 16
    CK_SESSION_HANDLE session = 0;
    unsigned long i, slot_count = SC_MAX_SLOT;
    CK_TOKEN_INFO token_info;
    CK_SLOT_ID slots[SC_MAX_SLOT];
    CK_SLOT_ID c_slot = SC_MAX_SLOT;
    CK_SLOT_ID slot = SC_MAX_SLOT;
    CK_RV rv  = 0;
    char msg[SC_STR_MAX_LEN] = "";
    
    sprintf(msg, "sc: sc_get_session called");
    logevent(f, msg);

    if(fl == 0) {
        sprintf(msg, "sc: Invalid state, no function list");
        goto err;
    }
    rv = fl->C_GetSlotList(TRUE, slots, &slot_count);
    if(CKR_OK != rv) {
        sprintf(msg, "sc: C_GetSlotList failed 0x%.4x", (int)rv);
        goto err;
    }

    sprintf(msg, "sc: slot_count = %d", (int)slot_count);
    logevent(f, msg);

    if(slot_count < 1) {
        sprintf(msg, "sc: No token available");
        goto err;
    }

    if (slot_count == 1) {
        char msg[SC_STR_MAX_LEN] = "";
        CK_TOKEN_INFO token_info;
        rv = fl->C_GetTokenInfo(slots[0],&token_info);
        sprintf(msg, "sc: forcing token label to the only allowed value: %s", token_info.label);
        c_slot = 0;
        logevent(f, msg);
    } else { 

        for(i=0; i<slot_count; i++) {
            slot = slots[i];
            rv = fl->C_GetTokenInfo(slot,&token_info);
            if (CKR_OK != rv) {
                sprintf(msg, "sc: C_GetTokenInfo failed for token in slot %i", i);
                goto err;
            }
            {
                char buf[40];
                memset(buf, 0, 40);
                strncpy(buf, token_info.label, 39);
                sprintf(msg, "sc: Found token in slot %i: %s", i, buf);
                logevent(f, msg);
                if(f) {
                    if(try_write_syslog) sc_write_syslog(msg);
                }
            }
            if(strncmp(token_label, token_info.label, strlen(token_label)) == 0) {
                c_slot = i;
                break;
            }
        }
        if(c_slot == 64) {
            sprintf(msg, "sc: No token named: %s", token_label);
            goto err;
        }              
    }
    rv = fl->C_OpenSession(slots[c_slot],CKF_SERIAL_SESSION|CKF_RW_SESSION, 0, 0, &session);
    if (CKR_OK != rv) {
        sprintf(msg, "sc: C_OpenSession failed");
        goto err;
    } else {
        if(f) logevent(f, "sc: Session opened");
    }
    return session;
 err:
    if(f) {
        logevent(f, msg);
        if(try_write_syslog) sc_write_syslog(msg);
    }
    //  m_fl->C_Finalize(0);
    //  m_fl = 0;
    return 0;
}

sc_token_list *sc_probe_library(const char *file, char **msg) {
    sc_token_list *tokens, *head = NULL;
    unsigned long i, slot_count = 16;
    CK_SLOT_ID slots[16];
    CK_FUNCTION_LIST_PTR fl = 0;
    HINSTANCE hLib = LoadLibrary(file);
    CK_C_GetFunctionList pGFL = (CK_RV(*)(CK_FUNCTION_LIST_PTR_PTR))GetProcAddress(hLib, "C_GetFunctionList");
    if (pGFL == NULL) {
	*msg = dupprintf("Bad PKCS#11 library!");
	return NULL;
    }
    if (pGFL(&fl) != CKR_OK) {
	*msg = dupprintf("Unable to load functions from PKCS#11 library!");
	return NULL;
    }
    if ((fl->C_Initialize(0) != CKR_OK)) {
	*msg = dupprintf("Unable to initialize PKCS#11 library!");
	return NULL;
    }
    if (fl->C_GetSlotList(TRUE, slots, &slot_count) != CKR_OK)
	goto cleanup;
    if (slot_count == 0)
	goto cleanup;
    tokens = malloc(sizeof(sc_token_list));
    if (tokens == NULL) {
	*msg = dupprintf("PKCS#11: Unable to allocate memory!");
	goto cleanup;
    }
    head = tokens;
    head->next = NULL;
    for (i = 0; i < slot_count; i++) {
	CK_SESSION_HANDLE session = 0;
	if (tokens == NULL)
	    tokens = malloc(sizeof(sc_token_list));
	if ((tokens != NULL) && (fl->C_GetTokenInfo(slots[i], &tokens->token_info)) == CKR_OK) {
	    char buf[32];
	    int j = 30;
	    memset(buf, 0, 32);
	    strncpy(buf, tokens->token_info.label, 31);
	    for (j = 30; (j > 0) && (buf[j] == ' '); j--)
		buf[j] = '\0';
	    tokens->token_label = calloc(sizeof(char), strlen(buf) + 1);
	    if (tokens->token_label != NULL)
		strcpy(tokens->token_label, buf);
	    if ((fl->C_OpenSession(slots[i], CKF_SERIAL_SESSION | CKF_RW_SESSION, 0, 0, &session) == CKR_OK) && session) {
		char msg[1024] = "";
		sc_cert_list *cl =
		    tokens->certs = sc_get_cert_list(fl, session, msg);
		tokens->cert_count = 0;
		while (cl != NULL) {
		    tokens->cert_count++;
		    cl = cl->next;
		}
		fl->C_CloseSession(session);
	    }
	    tokens = tokens->next;
	}
    }
cleanup:
    fl->C_Finalize(0);
    FreeLibrary(hLib);
    return head;
}

void sc_free_token_list(sc_token_list *tokens) {
    while (tokens != NULL) {
	sc_token_list *tl = tokens->next;
	if (tokens->token_label)
	    free(tokens->token_label);
	sc_free_cert_list(tokens->certs);
	free(tokens);
	tokens = tl;
    }
}

void sc_free_cert_list(sc_cert_list *cert_list) {
    sc_cert_list *cl = cert_list;
    while(cl != NULL) {
        sc_cert_list *next = cl->next;
        int i;
        for(i=0; i<sizeof(cl->cert_attr)/sizeof(CK_ATTRIBUTE); i++) {
            free(cl->cert_attr[i].pValue);
            cl->cert_attr[i].pValue = NULL;
        }
        free(cl);
        cl = next;
    }
    cert_list = NULL;
}

sc_cert_list *sc_get_cert_list(CK_FUNCTION_LIST_PTR fl, CK_SESSION_HANDLE session, char *err_msg) {
    CK_RV rv;
    /* STORE OBJECTS AND ATTRIBUTES */
    sc_cert_list *cl = NULL;
    sc_cert_list *pcl = NULL;
    CK_OBJECT_HANDLE list[SC_MAX_O];
    CK_ULONG i, found = 0;
    /* TEMPLATES: */
    CK_BBOOL        bFalse = 0;
    CK_BBOOL        bTrue = 1;
    CK_OBJECT_CLASS class_cert = CKO_CERTIFICATE;
    CK_ATTRIBUTE    cert_template[] = {
        { CKA_CLASS,    &class_cert,        sizeof (class_cert) },
        { CKA_TOKEN,    &bTrue,             sizeof (bTrue) },
        { CKA_PRIVATE,  &bFalse,            sizeof (bFalse) }
    };

    rv = fl->C_FindObjectsInit(session, cert_template, sizeof(cert_template)/sizeof(CK_ATTRIBUTE));
    if (CKR_OK != rv) {
        sprintf(err_msg, "sc: C_FindObjectsInit (certificate) failed, 0x%.4x", (int)rv);
        return NULL;
    }
    rv = fl->C_FindObjects(session, list, SC_MAX_O-1, &found);
    if (CKR_OK != rv) {
        sprintf(err_msg, "sc: C_FindObjects (certificate) failed, 0x%.4x", (int)rv);
        return NULL;
    }
    rv = fl->C_FindObjectsFinal(session);
    if (CKR_OK != rv) {
        sprintf(err_msg, "sc: C_FindObjectsFinal (certificate) failed, 0x%.4x", (int)rv);
        return NULL;
    }
    if (found < 1) {
        sprintf(err_msg, "sc: No certificate found");
        return NULL;
    }

    cl = calloc(1, sizeof(sc_cert_list));
    cl->cert_attr[0].type = CKA_LABEL; /* first element is the label of the cert */
    cl->cert_attr[1].type = CKA_ID;    /* second element is the id */
    cl->cert_attr[2].type = CKA_VALUE;    /* third element is the value -add risacher */
    pcl = cl;
    for(i=0; i<found; i++) {
        CK_OBJECT_HANDLE pO = list[i];
        rv = fl->C_GetAttributeValue(session, pO, pcl->cert_attr, sizeof(pcl->cert_attr)/sizeof(CK_ATTRIBUTE));
        if(CKR_OK == rv) {
            int nr;
            for(nr=0; nr<sizeof(pcl->cert_attr)/sizeof(CK_ATTRIBUTE); nr++) {
                pcl->cert_attr[nr].pValue = calloc(pcl->cert_attr[nr].ulValueLen+1, sizeof(char *));
            }
            rv = fl->C_GetAttributeValue(session, pO, pcl->cert_attr, sizeof(pcl->cert_attr)/sizeof(CK_ATTRIBUTE));
            if(CKR_OK == rv) {
                if(i<found-1) {
                    pcl->next = calloc(1, sizeof(sc_cert_list));
                    pcl = pcl->next;
                    pcl->cert_attr[0].type = CKA_LABEL;
                    pcl->cert_attr[1].type = CKA_ID;
                    pcl->cert_attr[2].type = CKA_VALUE;
                } else {
                    pcl->next = NULL;
                }
            } else {
                sprintf(err_msg, "sc: GetAttributeValue failed, no data for cert");
                for(nr=0; nr<sizeof(pcl->cert_attr)/sizeof(CK_ATTRIBUTE); nr++) {
                    free(pcl->cert_attr[nr].pValue);
                    pcl->cert_attr[nr].pValue = NULL;
                }
                free(pcl);
                pcl = NULL;
                return cl;
            }
        } else {
            sprintf(err_msg, "sc: GetAttributeValue failed (cert), 0x%.4x", (int)rv);
            free(pcl);
            pcl = NULL;
            return cl;
        }
    }   // for objects
    return cl;
}

void sc_free_pub_list(sc_pub_list *pub_list) {
    sc_pub_list *cl = pub_list;
    while(cl != NULL) {
        sc_pub_list *next = cl->next;
        int i;
        for(i=0; i<sizeof(cl->pub_attr)/sizeof(CK_ATTRIBUTE); i++) {
            free(cl->pub_attr[i].pValue);
            cl->pub_attr[i].pValue = NULL;
        }
        free(cl);
        cl = next;
    }
    pub_list = NULL;
}

sc_pub_list *sc_get_pub_list(CK_FUNCTION_LIST_PTR fl, CK_SESSION_HANDLE session, char *err_msg) {
    CK_RV rv;
    /* STORE OBJECTS AND ATTRIBUTES */
    sc_pub_list *pl = NULL;
    sc_pub_list *ppl = NULL;
    CK_OBJECT_HANDLE list[SC_MAX_O];
    CK_ULONG i, found = 0;
    /* TEMPLATES: */
    CK_BBOOL        bFalse = 0;
    CK_BBOOL        bTrue = 1;
    CK_OBJECT_CLASS class_public_key = CKO_PUBLIC_KEY;
    CK_KEY_TYPE     key_type  = CKK_RSA;
    CK_ATTRIBUTE    key_template[] = {
        { CKA_CLASS,    &class_public_key,  sizeof (class_public_key) },
        /*        { CKA_KEY_TYPE, &key_type,          sizeof (key_type) }, */
        { CKA_TOKEN,    &bTrue,             sizeof (bTrue) },
        { CKA_PRIVATE,  &bFalse,            sizeof (bFalse) }
    };

    rv = fl->C_FindObjectsInit(session, key_template, sizeof(key_template)/sizeof(CK_ATTRIBUTE));
    if (CKR_OK != rv) {
        sprintf(err_msg, "sc: C_FindObjectsInit (pub key) failed, 0x%.4x", (int)rv);
        return NULL;
    }
    rv = fl->C_FindObjects(session, list, SC_MAX_O-1, &found);
    if (CKR_OK != rv) {
        sprintf(err_msg, "sc: C_FindObjects (pub key) failed, 0x%.4x", (int)rv);
        return NULL;
    }
    rv = fl->C_FindObjectsFinal(session);
    if (CKR_OK != rv) {
        sprintf(err_msg, "sc: C_FindObjectsFinal (pub key) failed, 0x%.4x", (int)rv);
        return NULL;
    }
    if (found < 1) {
        sprintf(err_msg, "sc: No pub key found (beta)");
        return NULL;
    }

    pl = calloc(1, sizeof(sc_pub_list));
    pl->pub_attr[0].type = CKA_ID;
    pl->pub_attr[1].type = CKA_MODULUS_BITS;
    pl->pub_attr[2].type = CKA_MODULUS;
    pl->pub_attr[3].type = CKA_PUBLIC_EXPONENT;
    ppl = pl;
    for(i=0; i<found; i++) {
        CK_OBJECT_HANDLE pO = list[i];
        rv = fl->C_GetAttributeValue(session, pO, ppl->pub_attr, sizeof(ppl->pub_attr)/sizeof(CK_ATTRIBUTE));
        if(CKR_OK == rv) {
            int nr;
            for(nr=0; nr<sizeof(ppl->pub_attr)/sizeof(CK_ATTRIBUTE); nr++) {
                ppl->pub_attr[nr].pValue = calloc(ppl->pub_attr[nr].ulValueLen+1, sizeof(char *));
            }
            rv = fl->C_GetAttributeValue(session, pO, ppl->pub_attr, sizeof(ppl->pub_attr)/sizeof(CK_ATTRIBUTE));
            if(CKR_OK == rv) {
                if(i<found-1) {
                    ppl->next = calloc(1, sizeof(sc_pub_list));
                    ppl = ppl->next;
                    ppl->pub_attr[0].type = CKA_ID;
                    ppl->pub_attr[1].type = CKA_MODULUS_BITS;
                    ppl->pub_attr[2].type = CKA_MODULUS;
                    ppl->pub_attr[3].type = CKA_PUBLIC_EXPONENT;
                } else {
                    ppl->next = NULL;
                }
            } else {
                sprintf(err_msg, "sc: GetAttributeValue failed, no data for pub key");
                for(nr=0; nr<sizeof(ppl->pub_attr)/sizeof(CK_ATTRIBUTE); nr++) {
                    free(ppl->pub_attr[nr].pValue);
                    ppl->pub_attr[nr].pValue = NULL;
                }
                free(ppl);
                ppl = NULL;
                return pl;
            }
        } else {
            sprintf(err_msg, "sc: GetAttributeValue failed (pub), 0x%.4x", (int)rv);
            free(ppl);
            ppl = NULL;
            return pl;
        }
    }   // for objects

    return pl;
}


/* x509 Certificates are encoded in ASN.1 DER form */

/* find exponent and modulus (and lengths thereof) inside a cert.
   return 1 on success, 0 on failure */
int extract_key_from_cert(unsigned char* cert, int certsize, unsigned char **expo, unsigned char** modu, 
			  int* elen, int* mlen) {
  unsigned char *cursor = cert;
  int oidpos; 
  oidpos = find_substring(cursor, certsize, OIDrsaEncryption, sizeof(OIDrsaEncryption));
 
  if (oidpos != -1) { 
    cursor += oidpos;

    /* the OID, plus the NULL, consume 12 bytes */
    cursor += 12; /* skip OID and NULL */
    cursor += 2; /* skip 1st BIT STRING header */
    asn1_length(&cursor); /* skip length of 1st BIT STRING header */
    cursor += 2; /* skip 2nd BIT STRING header */
    asn1_length(&cursor); /* skip length of 2nd BIT STRING header */
    /* now we should be at the start of the ASN1 INTEGER for the pubkey (whew!) */
    if (02 == *(cursor++)) {
      *mlen = asn1_length(&cursor);
      if (*mlen == ~0) {return 0;}
      *modu = cursor;
      cursor += *mlen;
      if (02 == *(cursor++)) {
	*elen = asn1_length(&cursor);
	if (*elen == ~0) {return 0;}
	*expo = cursor;
	return 1;
      }
    }							      
  }
  *expo = NULL;
  *modu = NULL;
  return 0;
}

  

/* Given a handle pointing to an asn.1 BER/DER length field, return
   the length as an unsigned integer and update the handle to point
   just past the length.  Note that this obviously will fail horribly
   if the length field is larger than the size of an unsigned int; in
   which case it returns ~0 (-1). */
 
unsigned int asn1_length(unsigned char** cursor) {
  if (**cursor & 0x80) {
    /* long form */
    unsigned int length = 0;
    unsigned int lenlen = 0x7f & *((*cursor)++);
    unsigned int i;
    if (lenlen > sizeof (unsigned int)) { return ~0; }
    for (i=0; i< lenlen; i++) {
      length = ((length)<<8) + *((*cursor)++);
    }
    return length;
  } else {
    /* short form */
    return (unsigned int) *((*cursor)++);
  }
}

int find_substring(char* haystack, long haysize, const char* needle, long needlesize) 
{
  int i, j; 

  for (i=0; i< haysize-needlesize; i++) {
    for (j=0; j < needlesize; j++) {
      if (*(haystack+i+j) != *(needle+j)) {
	goto nope;
      }
    }
    return i;
  nope:
    j=0;
  }
  return -1;
}

unsigned char *generate_keystring(int *blob_len,
		unsigned char *expop, int elen,
		unsigned char *modup, int mlen) {
    unsigned char *blob, *p;

    *blob_len = 19 + elen + mlen;
    blob = calloc(sizeof(char *), *blob_len);
    p = blob;
    SC_PUT_32BIT(p, 7);
    p += 4;
    memcpy(p, "ssh-rsa", 7);
    p += 7;
    SC_PUT_32BIT(p, elen);
    p += 4;
    memcpy(p, expop, elen);
    p += elen;
    SC_PUT_32BIT(p, mlen);
    p += 4;
    memcpy(p, modup, mlen);
    
    return blob;
}

char *sc_get_keystring_from_cert(sc_cert_list *p) {
    unsigned char *expop, *modup, *pub_key;
    int elen, mlen, blob_len;

    extract_key_from_cert(p->cert_attr[2].pValue, p->cert_attr[2].ulValueLen, &expop, &modup, &elen, &mlen);
    pub_key = generate_keystring(&blob_len, expop, elen, modup, mlen);

    if (pub_key) {
	char *keystring;
	char *buffi = sc_base64key(pub_key, blob_len);
	keystring = calloc(1, strlen("ssh-rsa   ") + strlen(buffi) + p->cert_attr[0].ulValueLen);
	sprintf(keystring, "ssh-rsa %s %s", buffi, p->cert_attr[0].pValue);
	free(buffi);
	free(pub_key);
	return keystring;
    }
    return NULL;
}

unsigned char *sc_get_pubblob_from_cert(sc_cert_list *p, int *bloblen) {
    unsigned char *expop, *modup;
    int elen, mlen;

    extract_key_from_cert(p->cert_attr[2].pValue, p->cert_attr[2].ulValueLen, &expop, &modup, &elen, &mlen);
    return generate_keystring(bloblen, expop, elen, modup, mlen);
}

unsigned char *sc_get_pub(void *f, int try_write_syslog, sc_lib *sclib,
                          const char *token_label, const char *cert_label,
                          char **algorithm, int *blob_len) {
    /* return pub_key and blob_len */
    unsigned char *pub_key = NULL;
    sc_cert_list *cl;

    unsigned char *expop, *modup;
    int elen, mlen;

    /* some local helper: */
    char msg[SC_STR_MAX_LEN] = "";

    /* STORE OBJECTS AND ATTRIBUTES */
    CK_SESSION_HANDLE session = 0;

    sprintf(msg, "sc: Called sc_get_pub: token_label=%s, cert_label=%s", token_label, cert_label);
    logevent(f, msg);

    /* OPEN SESSION */    
    session = sc_get_session(f, try_write_syslog, sclib->m_fl, token_label);
    if(session == 0) {
        return NULL;
    }

    /* SEARCH THE SPECIFIED CERTIFICATE AND DETERMINE THE ID */
    {
        sc_cert_list *pcl;
        msg[0]='\0';
	cl = sc_get_cert_list(sclib->m_fl, session, msg);
        if(cl == NULL) goto err;
        if(strlen(msg) > 0) {
            logevent(f, msg);
            if(try_write_syslog) sc_write_syslog(msg);
        }
        pcl = cl;
        while(pcl != NULL) {
            unsigned int len = strlen(cert_label);
            if(pcl->cert_attr[0].ulValueLen < len) len = pcl->cert_attr[0].ulValueLen;
            if(strncmp(cert_label, pcl->cert_attr[0].pValue, len) == 0) {
                sclib->m_KeyID = calloc(sizeof(char *), pcl->cert_attr[1].ulValueLen+1);
                strncpy(sclib->m_KeyID, pcl->cert_attr[1].pValue, pcl->cert_attr[1].ulValueLen);
				{
					char *p_buf = calloc(1,pcl->cert_attr[0].ulValueLen+1);
					strncpy(p_buf, pcl->cert_attr[0].pValue, pcl->cert_attr[0].ulValueLen);
					sprintf(msg, "sc: Found cert attr[0]: %s", p_buf);
					free(p_buf);
				}
                logevent(f, msg);
                if(try_write_syslog) sc_write_syslog(msg);
                sprintf(msg, "sc: Found cert attr[1] : type 0x%x length 0x%x", pcl->cert_attr[1].type, pcl->cert_attr[1].ulValueLen);
                logevent(f, msg);
                extract_key_from_cert(pcl->cert_attr[2].pValue, pcl->cert_attr[2].ulValueLen,
                                      &expop, &modup,
                                      &elen, &mlen);
                if(try_write_syslog) sc_write_syslog(msg);
                break;
            }
            pcl = pcl->next;
        }
    }

    /* NOW GET THE PUB KEY FOR THIS CERT */
    if(sclib->m_KeyID == NULL) {
        sprintf(msg, "sc: No cert found (4) : %s", cert_label);
        goto err;
    } 
    if (NULL == expop) {
        /* this is the old code path that shouldn't ever happen any more */
        /* the key should already be extracted */
        sc_pub_list  *pl;
        sc_pub_list  *ppl;
        msg[0]='\0';
        
	pl = sc_get_pub_list(sclib->m_fl, session, msg);
        if(pl == NULL) goto err;
        if(strlen(msg) > 0) {
            logevent(f, msg);
            if(try_write_syslog) sc_write_syslog(msg);
        }
        ppl = pl;
        while(ppl != NULL) {
            sprintf(msg, "sc: trying ppl at 0x%x", ppl);
            logevent(f, msg);
            if(strncmp(sclib->m_KeyID, ppl->pub_attr[0].pValue, ppl->pub_attr[0].ulValueLen) == 0) {
                // attr 0: id
                // attr 2: modulus
                // attr 3: exponent
                {
                    char *p_buf = calloc(1, ppl->pub_attr[0].ulValueLen+1);
                    strncpy(p_buf, ppl->pub_attr[0].pValue, ppl->pub_attr[0].ulValueLen);
                    sprintf(msg, "sc: Found key: %s", p_buf);
                    free(p_buf);
                }
                logevent(f, msg);
                if(try_write_syslog) sc_write_syslog(msg);          
                
                //used in sclib free(expo);
                //free(modu);
                break;
            }
            ppl = ppl->next;
        }
        sc_free_pub_list(pl);
    }
    pub_key = generate_keystring(blob_len,
                                 expop, elen, 
                                 modup, mlen);
    if(sclib->rsakey != NULL) {
        free(sclib->rsakey->exponent);
        free(sclib->rsakey->modulus);
        free(sclib->rsakey);
    }
    sclib->rsakey = calloc(1, sizeof(struct RSAKey));
    sclib->rsakey->exponent = bignum_from_bytes(expop, elen);
    sclib->rsakey->modulus = bignum_from_bytes(modup, mlen);

    sclib->m_SshPK = calloc(sizeof(char *), *blob_len);
    memcpy(sclib->m_SshPK, pub_key, *blob_len);         
    sclib->m_SshPK_len = *blob_len;
    
    sclib->m_SshPk_alg = calloc(sizeof(char *), strlen("ssh-rsa")+1);
    strcpy(sclib->m_SshPk_alg, "ssh-rsa");
    *algorithm = sclib->m_SshPk_alg;

    {
        char *buffi = sc_base64key(pub_key, *blob_len);
        if (sclib->keystring) { free(sclib->keystring); }
        sclib->keystring = calloc (1, strlen("ssh-rsa   ")+strlen(buffi)+strlen(cert_label));
        sprintf(sclib->keystring, "ssh-rsa %s %s", buffi, cert_label);
        sprintf(msg, "sc: %s", sclib->keystring);
        logevent(f, msg);
        if(try_write_syslog) sc_write_syslog(msg);
        free(buffi);
    }

    if(sclib->m_SshPK == NULL) {
        sprintf(msg, "sc: No pub key found: %s", cert_label);
        goto err;
    }
    sclib->m_fl->C_CloseSession(session);
    sc_free_cert_list(cl);
    return pub_key;
    
 err:
    if (cl) { sc_free_cert_list(cl); }
    logevent(f, msg);
    if(try_write_syslog) sc_write_syslog(msg);
    sclib->m_fl->C_CloseSession(session);
    return NULL;
}

/* elements within sc_pubkey_blob must NOT be freed */
struct sc_pubkey_blob *sc_login_pub(void *f, int try_write_syslog, sc_lib *sclib,
                                    const char *token_label, const char *password) {
    CK_RV rv  = 0; 
    struct sc_pubkey_blob *key11;
    CK_SESSION_HANDLE session = 0;

    session = sc_get_session(f, try_write_syslog, sclib->m_fl, token_label);
    if(session == 0) {
        return NULL;
    }

    rv = sclib->m_fl->C_Login(session, CKU_USER, (CK_CHAR_PTR)password, strlen(password));
    if (CKR_OK != rv) {
        logevent(f, "sc: Login failed for public key");
        if(try_write_syslog) sc_write_syslog("sc: Login failed");
        sclib->m_fl->C_CloseSession(session);
        return (void *)SSH2_WRONG_PASSPHRASE;
    }

    logevent(f, "sc: Login successful");
  
    sclib->m_fl->C_Logout(session);
    sclib->m_fl->C_CloseSession(session);
  
    /* free when deleting sclib! */
    key11 = calloc(sizeof(struct sc_pubkey_blob), 1);
    key11->data = sclib->m_SshPK;
    key11->alg = sclib->m_SshPk_alg;
    key11->len = sclib->m_SshPK_len;

    return key11;
}


unsigned char *sc_sig(void *f, int try_write_syslog, sc_lib *sclib,
                      const char *token_label, const char *password_s,
                      char *sigdata, int sigdata_len, int *sigblob_len) {
    CK_RV rv  = 0; 
    char msg[SC_STR_MAX_LEN] = "";
    CK_SESSION_HANDLE session = 0;
    const char *pwd = password_s;
    /* TEMPLATES: */
    CK_BBOOL  bTrue = 1;
    CK_OBJECT_CLASS  class_private_key = CKO_PRIVATE_KEY;
    CK_KEY_TYPE      key_type  = CKK_RSA;
    CK_ATTRIBUTE key_template[] = {
        { CKA_CLASS,    &class_private_key,  sizeof (class_private_key) },
        { CKA_KEY_TYPE, &key_type,           sizeof (key_type) },
        { CKA_TOKEN,    &bTrue,              sizeof (bTrue) },
        { CKA_SIGN,     &bTrue,              sizeof (bTrue) },
        { CKA_PRIVATE,  &bTrue,              sizeof (bTrue) }
    };
    CK_ATTRIBUTE key_getattributes[] = { 
        {CKA_ID, NULL_PTR, 0},             /* ID to search the key */
        {CKA_MODULUS, NULL_PTR, 0}
    };
    /* STORE OBJECTS AND ATTRIBUTES */
    CK_OBJECT_HANDLE list[SC_MAX_O];
    CK_ULONG ii, found = 0;
    CK_OBJECT_HANDLE pO;

    unsigned char *ret = NULL;
    *sigblob_len = 0;

    session = sc_get_session(f, try_write_syslog, sclib->m_fl, token_label);
    if(session == 0) {
        return NULL;
    }
  
    rv = sclib->m_fl->C_Login(session, CKU_USER, (CK_CHAR_PTR)pwd, strlen(pwd));
    if (CKR_OK != rv) {
        logevent(f, "sc: Login failed in sc_sig");
        sclib->m_fl->C_CloseSession(session);
        return NULL;
    }
    rv = sclib->m_fl->C_FindObjectsInit(session, key_template, 4);
    if (CKR_OK != rv) {
        sprintf(msg, "sc: C_FindObjectsInit priv key failed, 0x%.4x", (int)rv);
        goto err;
    }
    rv = sclib->m_fl->C_FindObjects(session, list, SC_MAX_O-1, &found);
    if (CKR_OK != rv) {
        sprintf(msg, "sc: C_FindObjects priv key failed, 0x%.4x", (int)rv);
        goto err;
    } 
    rv = sclib->m_fl->C_FindObjectsFinal(session);
    if (CKR_OK != rv) {
        sprintf(msg, "sc: C_FindObjectsFinal priv key failed, 0x%.4x", (int)rv);
        goto err;
    }
    if (found < 1) {
        sprintf(msg, "sc: No priv keys found");
        goto err;
    }
    for(ii=0; ii<found; ii++) {
        int ts = 1;//sizeof (key_getattributes) / sizeof (CK_ATTRIBUTE);
        int nr;
		pO = list[ii];

        sc_write_syslog("1");
        for(nr=0;nr<ts;nr++) {
            key_getattributes[nr].ulValueLen = 0;
            key_getattributes[nr].pValue = NULL;
        }
        rv = sclib->m_fl->C_GetAttributeValue(session, pO, key_getattributes, ts);
        if(CKR_OK == rv) {
            for(nr=0;nr<ts;nr++) {
                key_getattributes[nr].pValue = calloc(sizeof(char *),key_getattributes[nr].ulValueLen+1);
            }
            if(sclib->m_fl->C_GetAttributeValue(session, pO, key_getattributes, ts) == CKR_OK) {
                if(strncmp(key_getattributes[0].pValue, sclib->m_KeyID, key_getattributes[0].ulValueLen) == 0) {
                    CK_BYTE signature[500];    
                    CK_ULONG signature_length = 500;
                    CK_MECHANISM mechanism = { CKM_RSA_PKCS, NULL_PTR, 0 };
                    unsigned char *bytes;
                    Bignum out;
                    int nbytes;
                    int r;
                    unsigned char hash_sha[20];
                    
                    char *p_buf = calloc(1, key_getattributes[0].ulValueLen+1);
                    strncpy(p_buf, key_getattributes[0].pValue, key_getattributes[0].ulValueLen);
                    sprintf(msg, "sc: Found pkey: %s", p_buf);
					free(p_buf);
                    logevent(f, msg);
                    if(try_write_syslog) sc_write_syslog(msg);
                    
                    rv = sclib->m_fl->C_SignInit(session, &mechanism, pO);
                    if (CKR_OK != rv) {
                        free(key_getattributes[0].pValue);
                        free(key_getattributes[1].pValue);
                        sprintf(msg, "sc: SignInit failed, 0x%.4x", (int)rv);
                        goto err;
                    }

                    /* rsa2_sign() */
                    SHA_Simple(sigdata, sigdata_len, hash_sha);
                    //        MD5Simple(sigdata, sigdata_len, hash_md5);
                    {
                        int j, message_len = sizeof(id_sha1) + sizeof(hash_sha);
                        CK_BYTE *message = calloc(sizeof(CK_BYTE), message_len);
                        for(j=0;j<sizeof(id_sha1);j++) message[j] = id_sha1[j]; 
                        memcpy((char *) &message[sizeof(id_sha1)], hash_sha, sizeof(hash_sha));
                        
                        rv = sclib->m_fl->C_Sign(session, message, message_len, signature, &signature_length);
						free(message);                 
						if (CKR_OK != rv) {
                            free(key_getattributes[0].pValue); 
                            free(key_getattributes[1].pValue); 
                            sprintf(msg, "sc: Sign failed, 0x%.4x", (int)rv);
                            goto err;
                        }
                    }

                    out = bignum_from_bytes(signature, signature_length);
                    nbytes = (bignum_bitcount(out) + 7) / 8;
                    *sigblob_len = 4 + 7 + 4 + nbytes;
                    bytes = calloc(sizeof(char *), *sigblob_len);
                    SC_PUT_32BIT(bytes, 7);
                    memcpy(bytes + 4, "ssh-rsa", 7);
                    SC_PUT_32BIT(bytes + 4 + 7, nbytes);
                    for (r = 0; r < nbytes; r++)
                        bytes[4 + 7 + 4 + r] = bignum_byte(out, nbytes - 1 - r);
                    ret = bytes;
                    
                    free(out);
                    free(key_getattributes[0].pValue); 
                    free(key_getattributes[1].pValue); 
                    break;
                }
            } else {
                logevent(f, "sc: GetAttributeValue failed, no data loaded");
            }
            free(key_getattributes[0].pValue); 
            free(key_getattributes[1].pValue); 
        } else {
            sprintf(msg, "sc: GetAttributeValue failed (pkey), 0x%.4x", (int)rv);
            logevent(f, msg);
            if(try_write_syslog) sc_write_syslog(msg);
        }
    }

    sclib->m_fl->C_Logout(session);
    sclib->m_fl->C_CloseSession(session);
    return ret;

 err:
    logevent(f, msg);
    if(try_write_syslog) sc_write_syslog(msg);
    sclib->m_fl->C_Logout(session);
    sclib->m_fl->C_CloseSession(session);
    if(ret != NULL) free(ret);
    /* just return an invalid signature ... */
    *sigblob_len = 1;
    return " ";
}
#endif /* DO_PKCS11_AUTH */
