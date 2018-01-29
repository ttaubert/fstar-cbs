/* This file was auto-generated by KreMLin! */
#include "kremlib.h"
#ifndef __CBS_H
#define __CBS_H


#include "Prims.h"
#include "Spec_Loops.h"


typedef struct 
{
  uint8_t *data;
  uint32_t len;
}
CBS_cbs_t;

uint8_t FStar_Seq_Properties_last__uint8_t(void *s);

bool CBS_cbs_get_u(CBS_cbs_t *cbs, uint32_t *out, uint32_t num);

bool CBS_cbs_get_u8(CBS_cbs_t *cbs, uint8_t *out);
#endif
