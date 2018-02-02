/* This file was auto-generated by KreMLin! */

#include "CBS.h"

bool CBS_cbs_skip(CBS_cbs_t *cbs, uint32_t num)
{
  CBS_cbs_t cbs0 = cbs[0U];
  CBS_cbs_t scrut0 = cbs0;
  uint32_t len = scrut0.len;
  uint32_t len0 = len;
  if (len0 >= num)
  {
    CBS_cbs_t scrut = cbs0;
    uint8_t *data = scrut.data;
    cbs[0U] = ((CBS_cbs_t){ .data = data + num, .len = len0 - num });
    return true;
  }
  else
    return false;
}

bool CBS_cbs_get(CBS_cbs_t *cbs, uint8_t **out, uint32_t num)
{
  CBS_cbs_t cbs0 = cbs[0U];
  CBS_cbs_t scrut = cbs0;
  uint32_t len = scrut.len;
  uint32_t len0 = len;
  if (len0 >= num)
  {
    CBS_cbs_t scrut = cbs0;
    uint8_t *data = scrut.data;
    out[0U] = data;
    return CBS_cbs_skip(cbs, num);
  }
  else
    return false;
}

bool CBS_cbs_get_u(CBS_cbs_t *cbs, uint32_t *out, uint32_t num)
{
  CBS_cbs_t cbs0 = cbs[0U];
  CBS_cbs_t scrut0 = cbs0;
  uint32_t len = scrut0.len;
  if (num > (uint32_t)0U && num < (uint32_t)5U && len >= num)
  {
    out[0U] = (uint32_t)0U;
    for (uint32_t i = (uint32_t)0U; i < num; i = i + (uint32_t)1U)
    {
      CBS_cbs_t scrut = cbs0;
      uint8_t *data = scrut.data;
      uint8_t bi = data[i];
      uint32_t lo = (uint32_t)bi;
      uint32_t uu____472 = out[0U];
      uint32_t hi = uu____472 << (uint32_t)8U;
      out[0U] = hi | lo;
    }
    return true;
  }
  else
    return false;
}

bool CBS_cbs_get_u8(CBS_cbs_t *cbs, uint8_t *out)
{
  CBS_cbs_t cbs0 = cbs[0U];
  CBS_cbs_t scrut = cbs0;
  uint32_t len = scrut.len;
  if (len > (uint32_t)0U)
  {
    CBS_cbs_t scrut = cbs0;
    uint8_t *data = scrut.data;
    uint8_t uu____542 = data[0U];
    out[0U] = uu____542;
    return true;
  }
  else
    return false;
}

bool CBS_cbs_get_u16(CBS_cbs_t *cbs, uint16_t *out)
{
  uint32_t num[1U] = { (uint32_t)0U };
  bool rv = CBS_cbs_get_u(cbs, num, (uint32_t)2U);
  uint32_t num0 = num[0U];
  out[0U] = (uint16_t)num0;
  return rv;
}

bool CBS_cbs_get_u24(CBS_cbs_t *cbs, uint32_t *out)
{
  return CBS_cbs_get_u(cbs, out, (uint32_t)3U);
}

bool CBS_cbs_get_u32(CBS_cbs_t *cbs, uint32_t *out)
{
  return CBS_cbs_get_u(cbs, out, (uint32_t)4U);
}

