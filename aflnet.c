#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <arpa/inet.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <unistd.h>

#include "alloc-inl.h"
#include "aflnet.h"

// Mapping from original state IDs to compact IDs starting from 1

static u32 message_code_counter = 0;
khash_t(32) *message_code_map = NULL;

void init_message_code_map(){
  message_code_map = kh_init(32);
}

void destroy_message_code_map(){
  kh_destroy(32, message_code_map);
}

u32 get_mapped_message_code (u32 ori_message_code){
  u32 mapped_message_code = 0;
  khiter_t k = kh_get(32, message_code_map, ori_message_code);
  if (k == kh_end(message_code_map)) {
    int ret;
    k = kh_put(32, message_code_map, ori_message_code, &ret);
    message_code_counter++;
    kh_value(message_code_map, k) = message_code_counter;

    mapped_message_code = message_code_counter;
  }
  else {
    mapped_message_code = kh_value(message_code_map, k);
  }

  return mapped_message_code;
}

// Protocol-specific functions for extracting requests and responses

region_t* extract_requests_tftp(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[2] = {0x00, 0x00};
  //char* terminator = '\0';
  mem = (char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  for (unsigned int byte_count = 0; byte_count < buf_size; byte_count++) {
    memcpy(&mem[mem_count], buf + byte_count, 1);
    if ((mem_count > 1) && (memcmp(&mem[mem_count - 1], terminator, 1) == 0)){
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;

        mem_count = 0;
        cur_start = cur_end + 1;
        cur_end = cur_start;

    }
    else {
      mem_count++;
      cur_end++;
      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }
      if (mem_count == mem_size) {

        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
    //ACTF("End of iteration");
  }
  if (mem) ck_free(mem);
  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}



// DHCP over UDP: the 236-byte BOOTP header, the magic cookie 63 82 53 63,
// then options (0 = pad, 255 = end, other codes: code, length, value). A
// message ends after its END option and the zero padding that follows it
// (BOOTP pads messages to 300 bytes). Returns the message length, or 0 when
// the framing does not parse; *type_ref receives the value of option 53
// (DHCP message type), 0 when absent.
static unsigned int dhcp_message_len(const unsigned char* b, unsigned int rem, unsigned int* type_ref)
{
  unsigned int p = 240;
  *type_ref = 0;
  if (rem < 241 || b[236] != 0x63 || b[237] != 0x82 || b[238] != 0x53 || b[239] != 0x63) return 0;
  while (p < rem) {
    if (b[p] == 0) { p++; continue; }
    if (b[p] == 255) {
      p++;
      while (p < rem && b[p] == 0) p++;
      return p;
    }
    if (p + 1 >= rem || b[p + 1] > rem - p - 2) return 0;
    if (b[p] == 53 && b[p + 1] >= 1 && !*type_ref) *type_ref = b[p + 2];
    p += 2 + b[p + 1];
  }
  return 0; // no END option
}

region_t* extract_requests_dhcp(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  // One region per message (one datagram each); a tail that does not parse
  // becomes one final region.
  region_t *regions = NULL;
  unsigned int region_count = 0, i = 0;

  while (i < buf_size) {
    unsigned int type, mlen = dhcp_message_len(buf + i, buf_size - i, &type);
    int framed = (mlen != 0);
    if (!framed) mlen = buf_size - i;
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = i + mlen - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    i += mlen;
    if (!framed) break;
  }

  *region_count_ref = region_count;
  return regions;
}


region_t* extract_requests_SNTP(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[1] = {0x0};
  //char* terminator = '\0';
  mem = (char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  for (unsigned int byte_count = 0; byte_count < buf_size; byte_count++) {
    memcpy(&mem[mem_count], buf + byte_count, 1);
    if ((mem_count > 1) && (memcmp(&mem[mem_count - 1], terminator, 1) == 0)){
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;

        mem_count = 0;
        cur_start = cur_end + 1;
        cur_end = cur_start;

    }
    else {
      mem_count++;
      cur_end++;
      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }
      if (mem_count == mem_size) {

        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
    //ACTF("End of iteration");
  }
  if (mem) ck_free(mem);
  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

region_t* extract_requests_NTP(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[1] = {0x0};
  //char* terminator = '\0';
  mem = (char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  if(buf_size==48){

    for (unsigned int byte_count = 0; byte_count < buf_size; byte_count++) {
    memcpy(&mem[mem_count], buf + byte_count, 1);
 
    if (mem_count==47){

        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;

        mem_count = 0;
        cur_start = cur_end + 1;
        cur_end = cur_start;

    }
    else {
      mem_count++;
      cur_end++;
      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }
      if (mem_count == mem_size) {

        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
    //ACTF("End of iteration");
    }
  }
  else{
    for (unsigned int byte_count = 0; byte_count < buf_size; byte_count++) {
      memcpy(&mem[mem_count], buf + byte_count, 1);
      if (((mem_count > 48) && (memcmp(&mem[mem_count - 1], terminator, 1) == 0) && (mem_count ==68 || mem_count==120))){
          region_count++;
          regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
          regions[region_count - 1].start_byte = cur_start;
          regions[region_count - 1].end_byte = cur_end;
          regions[region_count - 1].state_sequence = NULL;
          regions[region_count - 1].state_count = 0;

          mem_count = 0;
          cur_start = cur_end + 1;
          cur_end = cur_start;

      }
      else {
        mem_count++;
        cur_end++;
        //Check if the last byte has been reached
        if (cur_end == buf_size - 1) {
          region_count++;
          regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
          regions[region_count - 1].start_byte = cur_start;
          regions[region_count - 1].end_byte = cur_end;
          regions[region_count - 1].state_sequence = NULL;
          regions[region_count - 1].state_count = 0;
          break;
        }
        if (mem_count == mem_size) {

          //enlarge the mem buffer
          mem_size = mem_size * 2;
          mem=(char *)ck_realloc(mem, mem_size);
        }
      }
      //ACTF("End of iteration");
    }
  }
  if (mem) ck_free(mem);
  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

region_t* extract_requests_SNMP(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[1] = {0x0};
  //char* terminator = '\0';
  mem = (char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  for (unsigned int byte_count = 0; byte_count < buf_size; byte_count++) {
    memcpy(&mem[mem_count], buf + byte_count, 1);
    if ((mem_count > 1) && (memcmp(&mem[mem_count - 1], terminator, 1) == 0)){
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;

        mem_count = 0;
        cur_start = cur_end + 1;
        cur_end = cur_start;

    }
    else {
      mem_count++;
      cur_end++;
      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }
      if (mem_count == mem_size) {

        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
    //ACTF("End of iteration");
  }
  if (mem) ck_free(mem);
  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}


region_t* extract_requests_smtp(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
   char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[2] = {0x0D, 0x0A};

  mem=(char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  while (byte_count < buf_size) {

    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the last two bytes are 0x0D0A
    if ((mem_count > 1) && (memcmp(&mem[mem_count - 1], terminator, 2) == 0)) {
      region_count++;
      regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
      regions[region_count - 1].start_byte = cur_start;
      regions[region_count - 1].end_byte = cur_end;
      regions[region_count - 1].state_sequence = NULL;
      regions[region_count - 1].state_count = 0;

      mem_count = 0;
      cur_start = cur_end + 1;
      cur_end = cur_start;
    } else {
      mem_count++;
      cur_end++;

      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }

      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);

  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

region_t* extract_requests_ssh(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[2] = {0x0D, 0x0A};

  mem=(char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  while (byte_count < buf_size) {

    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the region buffer length is at least 6 bytes
    //Why 6 bytes? It is because both the SSH identification and the normal message are longer than 6 bytes
    //For normal message, it starts with message size (4 bytes), #padding_bytes (1 byte) and message code (1 byte)
    if (mem_count >= 6) {
      if (!strncmp(mem, "SSH-", 4)) {
        //It could be an identification message
        //Find terminator (0x0D 0x0A)
        while ((byte_count < buf_size) && (memcmp(&mem[mem_count - 1], terminator, 2))) {
          if (mem_count == mem_size - 1) {
            //enlarge the mem buffer
            mem_size = mem_size * 2;
            mem=(char *)ck_realloc(mem, mem_size);
          }
          memcpy(&mem[++mem_count], buf + byte_count++, 1);
          cur_end++;
        }

        //Create one region
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;

        //Check if the last byte has been reached
        if (cur_end < buf_size - 1) {
          mem_count = 0;
          cur_start = cur_end + 1;
          cur_end = cur_start;
        }
      } else {
        //It could be a normal message
        //Extract the message size stored in the first 4 bytes
        unsigned int* size_buf = (unsigned int*)&mem[0];
        unsigned int message_size = (unsigned int)ntohl(*size_buf);
        unsigned char message_code = (unsigned char)mem[5];
        //and skip the payload and the MAC
        unsigned int bytes_to_skip = message_size - 2;
        if ((message_code >= 20) && (message_code <= 49)) {
          //Do nothing
        } else {
          bytes_to_skip += 8;
        }

        unsigned int temp_count = 0;
        while ((byte_count < buf_size) && (temp_count < bytes_to_skip)) {
          byte_count++;
          cur_end++;
          temp_count++;
        }

        if (byte_count < buf_size) {
          byte_count--;
          cur_end--;
        }

        //Create one region
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;

        //Check if the last byte has been reached
        if (cur_end < buf_size - 1) {
          mem_count = 0;
          cur_start = cur_end + 1;
          cur_end = cur_start;
        }
      }
    } else {
      mem_count++;
      cur_end++;

      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }

      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);

  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

region_t* extract_requests_tls(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;

  mem=(char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  while (byte_count < buf_size) {

    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the region buffer length is at least 5 bytes (record header size)
    if (mem_count >= 5) {
      //1st byte: content type
      //2nd and 3rd byte: TLS version
      //Extract the message size stored in the 4th and 5th bytes
      u16* size_buf = (u16*)&mem[3];
      u16 message_size = (u16)ntohs(*size_buf);

      //and skip the payload
      unsigned int bytes_to_skip = message_size;

      unsigned int temp_count = 0;
      while ((byte_count < buf_size) && (temp_count < bytes_to_skip)) {
        byte_count++;
        cur_end++;
        temp_count++;
      }

      if (byte_count < buf_size) {
          byte_count--;
          cur_end--;
      }

      //Create one region
      region_count++;
      regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
      regions[region_count - 1].start_byte = cur_start;
      regions[region_count - 1].end_byte = cur_end;
      regions[region_count - 1].state_sequence = NULL;
      regions[region_count - 1].state_count = 0;

      //Check if the last byte has been reached
      if (cur_end < buf_size - 1) {
        mem_count = 0;
        cur_start = cur_end + 1;
        cur_end = cur_start;
      }
    } else {
      mem_count++;
      cur_end++;

      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }

      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);

  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}


region_t* extract_requests_dicom(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  unsigned int pdu_length = 0;
  unsigned int packet_length = 0;
  unsigned int region_count = 0;
  unsigned int end = 0;
  unsigned int start = 0;

  region_t *regions = NULL;

  unsigned int byte_count = 0;
  while (byte_count < buf_size) {

    if ((byte_count + 2 >= buf_size) || (byte_count + 5 >= buf_size)) break;

    // Bytes from third to sixth encode the PDU length.
    pdu_length =
      (buf[byte_count + 5]) |
      (buf[byte_count + 4] << 8)  |
      (buf[byte_count + 3] << 16) |
      (buf[byte_count + 2] << 24);

    // DICOM Header(6 bytes) includes PDU type and PDU length.
    packet_length = pdu_length + 6;

    start = byte_count;
    end = byte_count + packet_length - 1;

    if (end < start) break; // it means that int overflow has happened -_0_0_-
    if (end >= buf_size) break; // checking boundaries

    region_count++;
    regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
    regions[region_count - 1].start_byte = start;
    regions[region_count - 1].end_byte = end;
    regions[region_count - 1].state_sequence = NULL;
    regions[region_count - 1].state_count = 0;

    if ( (byte_count + packet_length) < byte_count ) break; // checking int overflow
    if ( (byte_count + packet_length) < packet_length ) break; // checking int overflow
    byte_count += packet_length;
  }

  // if bytes is left
  if ((byte_count < buf_size) && (buf_size > 0)) {
    region_count++;
    regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
    regions[region_count - 1].start_byte = byte_count;
    regions[region_count - 1].end_byte = buf_size - 1;
    regions[region_count - 1].state_sequence = NULL;
    regions[region_count - 1].state_count = 0;
  }

  *region_count_ref = region_count;
  return regions;
}

region_t* extract_requests_dns(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;

  mem = (char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  for (unsigned int byte_count = 0; byte_count < buf_size; byte_count++) {
    memcpy(&mem[mem_count], buf + byte_count, 1);

    // A DNS header is 12 bytes long & the 1st null byte after that indicates the end of the query.
    if ((mem_count >= 12) && (*(mem+mem_count) == 0)) {
      // 4 bytes left of the tail.
      cur_end += 4;
      byte_count += 4;
      region_count++;
      regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
      regions[region_count - 1].start_byte = cur_start;
      regions[region_count - 1].end_byte = cur_end;
      regions[region_count - 1].state_sequence = NULL;
      regions[region_count - 1].state_count = 0;

      if (cur_end == buf_size - 1) break;

      mem_count = 0;
      cur_start = cur_end + 1;
      cur_end = cur_start;
    } else {
      mem_count++;
      cur_end++;

      // Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }

      if (mem_count == mem_size) {
        // Enlarge the mem buffer
        mem_size *= 2;
        mem = (char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);

  // In case region_count equals zero, it means that the structure of the buffer is broken
  // hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

region_t* extract_requests_rtsp(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[4] = {0x0D, 0x0A, 0x0D, 0x0A};

  mem=(char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  while (byte_count < buf_size) {

    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the last four bytes are 0x0D0A0D0A
    if ((mem_count > 3) && (memcmp(&mem[mem_count - 3], terminator, 4) == 0)) {
      region_count++;
      regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
      regions[region_count - 1].start_byte = cur_start;
      regions[region_count - 1].end_byte = cur_end;
      regions[region_count - 1].state_sequence = NULL;
      regions[region_count - 1].state_count = 0;

      mem_count = 0;
      cur_start = cur_end + 1;
      cur_end = cur_start;
    } else {
      mem_count++;
      cur_end++;

      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }

      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);

  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

region_t* extract_requests_ftp(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[2] = {0x0D, 0x0A};

  mem=(char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  while (byte_count < buf_size) {

    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the last two bytes are 0x0D0A
    if ((mem_count > 1) && (memcmp(&mem[mem_count - 1], terminator, 2) == 0)) {
      region_count++;
      regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
      regions[region_count - 1].start_byte = cur_start;
      regions[region_count - 1].end_byte = cur_end;
      regions[region_count - 1].state_sequence = NULL;
      regions[region_count - 1].state_count = 0;

      mem_count = 0;
      cur_start = cur_end + 1;
      cur_end = cur_start;
    } else {
      mem_count++;
      cur_end++;

      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }

      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);

  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

// MQTT control packet: one type/flags byte, the Remaining Length as a
// variable byte integer (1-4 bytes, 7 bits each, top bit = more), then that
// many bytes. Returns the packet length, or 0 when the buffer does not hold
// a complete, well-formed packet; *hdrlen receives the fixed header length.
static unsigned int mqtt_packet_len(const unsigned char* b, unsigned int rem, unsigned int* hdrlen)
{
  unsigned int value = 0, shift = 0, k;
  for (k = 1; k <= 4; k++) {
    if (k >= rem) return 0;
    value |= (unsigned int)(b[k] & 0x7f) << shift;
    if (!(b[k] & 0x80)) {
      if (value > rem - 1 - k) return 0;
      *hdrlen = 1 + k;
      return 1 + k + value;
    }
    shift += 7;
  }
  return 0;
}

region_t* extract_requests_mqtt(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  // One region per packet; a truncated or malformed tail becomes one final
  // region, so the regions always cover exactly the buffer.
  region_t *regions = NULL;
  unsigned int region_count = 0, i = 0;

  while (i < buf_size) {
    unsigned int hdrlen, plen = mqtt_packet_len(buf + i, buf_size - i, &hdrlen);
    int framed = (plen != 0);
    if (!framed) plen = buf_size - i;
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = i + plen - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    i += plen;
    if (!framed) break;
  }

  *region_count_ref = region_count;
  return regions;
}

region_t* extract_requests_sip(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[2] = {0x0D, 0x0A};

  mem=(char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  while (byte_count < buf_size) {

    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the last bytes match the terminator, and the next ones are a SIP command
    if ((mem_count > 1) && (memcmp(&mem[mem_count - 1], terminator, 1) == 0) &&
	  (((buf_size - byte_count >= 8) && (memcmp(buf + byte_count, "REGISTER", 8)==0) ) ||
	  ((buf_size - byte_count >= 6) && (memcmp(buf + byte_count, "INVITE", 6)==0) ) ||
	  ((buf_size - byte_count >= 3) && (memcmp(buf + byte_count, "ACK", 3)==0) ) ||
	  ((buf_size - byte_count >= 3) && (memcmp(buf + byte_count, "BYE", 3)==0) ) )
	  ) {
      region_count++;
      regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
      regions[region_count - 1].start_byte = cur_start;
      regions[region_count - 1].end_byte = cur_end;
      regions[region_count - 1].state_sequence = NULL;
      regions[region_count - 1].state_count = 0;

      mem_count = 0;
      cur_start = cur_end + 1;
      cur_end = cur_start;
    } else {
      mem_count++;
      cur_end++;

      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }

      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);

  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

region_t* extract_requests_http(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[4] = {0x0D, 0x0A, 0x0D, 0x0A};

  mem=(char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  while (byte_count < buf_size) {

    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the last four bytes are 0x0D0A0D0A
    if ((mem_count >=4) && (memcmp(&mem[mem_count - 3], terminator, 4) == 0)) {
      region_count++;
      regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
      regions[region_count - 1].start_byte = cur_start;
      regions[region_count - 1].end_byte = cur_end;
      regions[region_count - 1].state_sequence = NULL;
      regions[region_count - 1].state_count = 0;

      mem_count = 0;
      cur_start = cur_end + 1;
      cur_end = cur_start;
    } else {
      mem_count++;
      cur_end++;

      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }

      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);

  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

region_t* extract_requests_ipp(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  char terminator[4] = {0x0D, 0x0A, 0x0D, 0x0A};
  char ipp[1] = {0x03};

  mem=(char *)ck_alloc(mem_size);

  unsigned int cur_start = 0;
  unsigned int cur_end = 0;
  while (byte_count < buf_size) {

    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the last bytes match the HTTP terminator (if data is sent) OR end-of-attributes-tag IPP command (if no data is sent)
    if ((mem_count > 3) && 
    ((memcmp(&mem[mem_count - 3], terminator, 4) == 0) || (memcmp(&mem[mem_count], ipp, 1) == 0)) &&
    ((buf_size - byte_count >= 4) && (memcmp(buf + byte_count, "POST", 4) == 0))
    ) {
      region_count++;
      regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
      regions[region_count - 1].start_byte = cur_start;
      regions[region_count - 1].end_byte = cur_end;
      regions[region_count - 1].state_sequence = NULL;
      regions[region_count - 1].state_count = 0;

      mem_count = 0;
      cur_start = cur_end + 1;
      cur_end = cur_start;
    } else {
      mem_count++;
      cur_end++;

      //Check if the last byte has been reached
      if (cur_end == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = cur_end;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }

      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);

  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

// Parse a CRLF-terminated decimal number (with optional '-') starting at
// offset, e.g. the "3" of "*3\r\n" or the "-1" of "$-1\r\n". Returns 1 and
// fills *value and *next_off (the first byte after the CRLF) on success;
// returns 0 on malformed input or if the line does not fit in the buffer.
static int read_resp_number(unsigned char* buf, unsigned int buf_size, unsigned int offset, int* value, unsigned int* next_off) {
  unsigned int i = offset;
  int sign = 1;
  long v = 0;

  if (i >= buf_size) return 0;
  if (buf[i] == '-') {
    sign = -1;
    i++;
  }
  if (i >= buf_size) return 0;
  if (!isdigit(buf[i])) return 0;

  while ((i < buf_size) && isdigit(buf[i])) {
    v = v * 10 + (buf[i] - '0');
    if (v > 0xFFFFFF) return 0; // sanity cap to keep the arithmetic in range
    i++;
  }

  if ((i + 1 >= buf_size) || (buf[i] != 0x0D) || (buf[i + 1] != 0x0A)) return 0;

  *value = (int)(sign * v);
  *next_off = i + 2;
  return 1;
}

// RESP (REdis Serialization Protocol) request splitting. A client command is
// either a multibulk array ("*N\r\n" followed by N "$len\r\n<data>\r\n" bulk
// strings) or a plain inline command terminated by CRLF. The whole array (or
// the whole line) is one request message.
region_t* extract_requests_resp(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  unsigned int byte_count = 0;
  unsigned int region_count = 0;
  region_t *regions = NULL;

  while (byte_count < buf_size) {
    unsigned int start = byte_count;
    unsigned int end = buf_size - 1;
    int valid = 0;

    if (buf[byte_count] == '*') {
      // Multibulk command
      int count = 0;
      unsigned int off = 0;

      if (read_resp_number(buf, buf_size, byte_count + 1, &count, &off) && (count >= 0)) {
        int i;
        valid = 1;
        for (i = 0; i < count; i++) {
          int len = 0;
          unsigned int data_off = 0;

          if ((off >= buf_size) || (buf[off] != '$')) {
            valid = 0;
            break;
          }
          if (!read_resp_number(buf, buf_size, off + 1, &len, &data_off)) {
            valid = 0;
            break;
          }
          if (len < 0) {
            valid = 0; // null bulk strings cannot appear inside a command
            break;
          }
          if ((unsigned int)len > buf_size - data_off) {
            valid = 0; // bulk data overruns the buffer
            break;
          }
          off = data_off + len;
          if ((off + 1 >= buf_size) || (buf[off] != 0x0D) || (buf[off + 1] != 0x0A)) {
            valid = 0;
            break;
          }
          off += 2;
        }
        if (valid) end = off - 1;
      }
    } else {
      // Inline command: everything up to and including the first CRLF
      unsigned int i;
      for (i = byte_count; (i + 1) < buf_size; i++) {
        if ((buf[i] == 0x0D) && (buf[i + 1] == 0x0A)) {
          end = i + 1;
          valid = 1;
          break;
        }
      }
    }

    if (!valid) {
      // Malformed framing -- the remainder of the buffer becomes one region
      end = buf_size - 1;
      byte_count = buf_size;
    } else {
      byte_count = end + 1;
    }

    region_count++;
    regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
    regions[region_count - 1].start_byte = start;
    regions[region_count - 1].end_byte = end;
    regions[region_count - 1].state_sequence = NULL;
    regions[region_count - 1].state_count = 0;
  }

  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

unsigned int* extract_response_codes_tftp(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  char terminator_one[1] = {0x00};
  char terminator_two[1] = {0x03};

  mem=(char *)ck_alloc(mem_size);

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {
    memcpy(&mem[mem_count], buf + byte_count++, 1);

    if ((mem_count > 0) && ((memcmp(&mem[mem_count - 1], terminator_one, 1) == 0) || (memcmp(&mem[mem_count - 1], terminator_two, 1) == 0))) {
      //Extract the response code which is the first 4 bytes
      char temp[5];
      memcpy(temp, mem, 5);
      temp[4] = 0x0;
      unsigned int message_code = (unsigned int) atoi(temp);

      if (message_code == 0) break;

      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      mem_count = 0;
    } else if (byte_count == buf_size){
      char temp[5];
      memcpy(temp, mem, 5);
      temp[4] = 0x0;
      unsigned int message_code = (unsigned int) atoi(temp);
      if (message_code == 0) break;

      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      //mem_count = 0;
      break;
    }else{
      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_dhcp(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // One code per reply: its DHCP message type (option 53: 2 OFFER, 5 ACK,
  // 6 NAK, ...), or 0x100 for a plain BOOTP reply without one. Stops at a
  // reply that does not parse.
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0, i = 0;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (i < buf_size) {
    unsigned int type, mlen = dhcp_message_len(buf + i, buf_size - i, &type);
    if (!mlen) break;
    state_count++;
    state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
    state_sequence[state_count - 1] = type ? type : 0x100;
    i += mlen;
  }

  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_SNTP(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  char terminator_one[1] = {0x24};
  char terminator_two[1] = {0x35};
  char terminator_three[1] = {0x01};
  

  mem=(char *)ck_alloc(mem_size);

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {
    memcpy(&mem[mem_count], buf + byte_count++, 1);

    if ((mem_count > 0) && ((memcmp(&mem[mem_count - 1], terminator_one, 1) == 0) || (memcmp(&mem[mem_count - 1], terminator_two, 1) == 0)
    ||(memcmp(&mem[mem_count - 1], terminator_three, 1) == 0))) {
      //Extract the response code which is the first 4 bytes
     
      char temp[5];
      memcpy(temp, mem, 5);
      
      unsigned int message_code = (unsigned int)temp;
      if (message_code == 0)
      {
        break;

      } 

      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      mem_count = 0;
    } else if (byte_count == buf_size){
      char temp[5];
      memcpy(temp, mem, 5);
      temp[4] = 0x0;
      unsigned int message_code = (unsigned int) atoi(temp);
      if (message_code == 0) {
        break;
      }

      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      //mem_count = 0;
      break;
    }else{
      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_NTP(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  char terminator_one[1] = {0x24};
  char terminator_two[1] = {0x35};
  char terminator_three[1] = {0x01};
  

  mem=(char *)ck_alloc(mem_size);

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {
    memcpy(&mem[mem_count], buf + byte_count++, 1);

    if ((mem_count > 0) && ((memcmp(&mem[mem_count - 1], terminator_one, 1) == 0) || (memcmp(&mem[mem_count - 1], terminator_two, 1) == 0)
    ||(memcmp(&mem[mem_count - 1], terminator_three, 1) == 0))) {
      //Extract the response code which is the first 4 bytes
      char temp[5];
      memcpy(temp, mem, 5);
      
      unsigned int message_code = (unsigned int)temp;
      if (message_code == 0)
      {
        break;

      }
      
      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      mem_count = 0;
    } else if (byte_count == buf_size){
      char temp[5];
      memcpy(temp, mem, 5);
      temp[4] = 0x0;
      unsigned int message_code = (unsigned int) atoi(temp);
      if (message_code == 0) {
        break;
      }

      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      //mem_count = 0;
      break;
    }else{
      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}


unsigned int* extract_response_codes_SNMP(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  char terminator_one[1] = {0x0A};
  char terminator_two[1] = {0x01};
  char terminator_three[1] = {0x02};
  char terminator_four[1] = {0x03};
  char terminator_five[1] = {0x04};
  char terminator_six[1] = {0x05};
  

  mem=(char *)ck_alloc(mem_size);

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {
    memcpy(&mem[mem_count], buf + byte_count++, 1);
    

    if ((mem_count>7) && ((memcmp(&mem[mem_count - 1], terminator_one, 1) == 0) || (memcmp(&mem[mem_count - 1], terminator_two, 1) == 0)
    ||(memcmp(&mem[mem_count - 1], terminator_three, 1) == 0)||(memcmp(&mem[mem_count-1],terminator_four,1)==0) || (memcmp(&mem[mem_count-1],terminator_five,1)==0)
    ||(memcmp(&mem[mem_count-1],terminator_six,1)==0))) {
      //Extract the response code which is the first 4 bytes
      char temp[2];
      memcpy(temp, &mem[byte_count-1], 1);
      temp[1] = 0x0;
      unsigned int message_code = (unsigned int)(temp);
      if (message_code == 0)
      {
        break;

      } 

      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      mem_count = 0;
    } else if (byte_count == buf_size){
      char temp[2];
      memcpy(temp, &mem[byte_count-1], 1);
      temp[1] = 0x0;
      unsigned int message_code = (unsigned int)(temp);
      if (message_code == 0) {
        break;
      }

      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      //mem_count = 0;
      break;
    }else{
      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}
unsigned int* extract_response_codes_smtp(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  char terminator[2] = {0x0D, 0x0A};

  mem=(char *)ck_alloc(mem_size);

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {
    memcpy(&mem[mem_count], buf + byte_count++, 1);

    if ((mem_count > 0) && (memcmp(&mem[mem_count - 1], terminator, 2) == 0)) {
      //Extract the response code which is the first 3 bytes
      char temp[4];
      memcpy(temp, mem, 4);
      temp[3] = 0x0;
      unsigned int message_code = (unsigned int) atoi(temp);

      if (message_code == 0) break;

      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      mem_count = 0;
    } else {
      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_ssh(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
   char mem[7];
   unsigned int byte_count = 0;
   unsigned int *state_sequence = NULL;
   unsigned int state_count = 0;

   //Initial state
   state_count++;
   state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
   if (state_sequence == NULL) PFATAL("Unable realloc a memory region to store state sequence");
   state_sequence[state_count - 1] = 0;

   while (byte_count < buf_size) {
      memcpy(mem, buf + byte_count, 6);
      byte_count += 6;

      /* If this is the identification message */
      if (strstr(mem, "SSH")) {
        //Read until \x0D\x0A
        char tmp = 0x00;
        while (tmp != 0x0A) {
          memcpy(&tmp, buf + byte_count, 1);
          byte_count += 1;
        }
        state_count++;
        state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
        if (state_sequence == NULL) PFATAL("Unable realloc a memory region to store state sequence");
        state_sequence[state_count - 1] = 256; //Identification
      } else {
        //Extract the message type and skip the payload and the MAC
        unsigned int* size_buf = (unsigned int*)&mem[0];
        unsigned int message_size = (unsigned int)ntohl(*size_buf);

        //Break if the response does not adhere to the known format(s)
        //Normally, it only happens in the last response
        if (message_size - 2 > buf_size - byte_count) break;

        unsigned char message_code = (unsigned char)mem[5];
        
        /* If this is a KEY exchange related message */
        if ((message_code >= 20) && (message_code <= 49)) {
          //Do nothing
        } else {
          message_size += 8;
        }

        message_code = get_mapped_message_code(message_code);

        state_count++;
        state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
        if (state_sequence == NULL) PFATAL("Unable realloc a memory region to store state sequence");
        state_sequence[state_count - 1] = message_code;

        byte_count += message_size - 2;
      }
   }
   *state_count_ref = state_count;
   return state_sequence;
}

unsigned int* extract_response_codes_tls(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned char content_type, message_type;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;

  mem=(char *)ck_alloc(mem_size);

  //Add initial state
  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {

    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the region buffer length is at least 6 bytes (5 bytes for record header size)
    //the 6th byte could be message type
    if (mem_count >= 6) {
      //1st byte: content type
      //2nd and 3rd byte: TLS version
      //Extract the message size stored in the 4th and 5th bytes
      content_type = mem[0];

      //Check if this is an application data record
      if (content_type != 0x17) {
        message_type = mem[5];
      } else {
        message_type = 0xFF;
      }

      u16* size_buf = (u16*)&mem[3];
      u16 message_size = (u16)ntohs(*size_buf);

      //and skip the payload
      unsigned int bytes_to_skip = message_size - 1;
      unsigned int temp_count = 0;
      while ((byte_count < buf_size) && (temp_count < bytes_to_skip)) {
        byte_count++;
        temp_count++;
      }

      if (byte_count < buf_size) {
          byte_count--;
      }

      //add a new response code
      unsigned int message_code = (content_type << 8) + message_type;
      message_code = get_mapped_message_code(message_code);
      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      mem_count = 0;
    } else {
      mem_count++;

      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);

  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_dicom(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  if (buf_size == 0) {
    *state_count_ref = 0;
    return NULL;
  }

  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0; // initial status code is 0

  state_count++;
  unsigned int message_code = buf[0]; // return PDU type as status code
  message_code = get_mapped_message_code(message_code);
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = message_code;

  *state_count_ref = state_count;
  return state_sequence;
};

unsigned int* extract_response_codes_dns(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;

  mem=(char *)ck_alloc(mem_size);

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  for (unsigned int byte_count = 0; byte_count < buf_size; byte_count++) {
    memcpy(&mem[mem_count], buf + byte_count, 1);

    // The original query will be included with the response.
    if ((mem_count >= 12) && (*(mem+mem_count) == 0)) {
      // 4 bytes left of the query. Jump to the answer.
      byte_count += 5;
      mem_count += 5;

      // Save the 3rd & 4th bytes as the response code
      unsigned int message_code = (unsigned int) ((mem[2] << 8) + mem[3]);
      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      mem_count = 0;
    } else {
      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}

static unsigned char dtls12_version[2] = {0xFE, 0xFD};

// (D)TLS known and custom constants

// the known 1-byte (D)TLS content types
#define CCS_CONTENT_TYPE 0x14
#define ALERT_CONTENT_TYPE 0x15
#define HS_CONTENT_TYPE 0x16
#define APPLICATION_CONTENT_TYPE 0x17
#define HEARTBEAT_CONTENT_TYPE 0x18

// custom content types
#define UNKNOWN_CONTENT_TYPE 0xFF // the content type is unrecognized

// custom handshake types (for handshake content)
#define UNKNOWN_MESSAGE_TYPE 0xFF // when the message type cannot be determined because the message is likely encrypted
#define MALFORMED_MESSAGE_TYPE 0xFE // when message type cannot be determined because the message appears to be malformed

region_t *extract_requests_dtls12(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref) {
  unsigned int byte_count = 0;
  unsigned int region_count = 0;
  region_t *regions = NULL;

  unsigned int cur_start = 0;

   while (byte_count < buf_size) {

     //Check if the first three bytes are <valid_content_type><dtls-1.2>
     if ((byte_count > 3 && buf_size - byte_count > 1) &&
     (buf[byte_count] >= CCS_CONTENT_TYPE && buf[byte_count] <= HEARTBEAT_CONTENT_TYPE)  &&
     (memcmp(&buf[byte_count+1], dtls12_version, 2) == 0)) {
       region_count++;
       regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
       regions[region_count - 1].start_byte = cur_start;
       regions[region_count - 1].end_byte = byte_count-1;
       regions[region_count - 1].state_sequence = NULL;
       regions[region_count - 1].state_count = 0;
       cur_start = byte_count;
     } else {

      //Check if the last byte has been reached
      if (byte_count == buf_size - 1) {
        region_count++;
        regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
        regions[region_count - 1].start_byte = cur_start;
        regions[region_count - 1].end_byte = byte_count;
        regions[region_count - 1].state_sequence = NULL;
        regions[region_count - 1].state_count = 0;
        break;
      }
     }

     byte_count ++;
  }

  //in case region_count equals zero, it means that the structure of the buffer is broken
  //hence we create one region for the whole buffer
  if ((region_count == 0) && (buf_size > 0)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0;
    regions[0].end_byte = buf_size - 1;
    regions[0].state_sequence = NULL;
    regions[0].state_count = 0;

    region_count = 1;
  }

  *region_count_ref = region_count;
  return regions;
}

// a status code comprises <content_type, message_type> tuples
// message_type varies depending on content_type (e.g. for handshake content, message_type is the handshake message type...)
//
unsigned int* extract_response_codes_dtls12(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  unsigned int byte_count = 0;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  unsigned int status_code = 0;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0; // initial status code is 0

  while (byte_count < buf_size) {
    // a DTLS 1.2 record has a 13 bytes header, followed by the contained message
    if ( (buf_size - byte_count > 13) &&
    (buf[byte_count] >= CCS_CONTENT_TYPE && buf[byte_count] <= HEARTBEAT_CONTENT_TYPE)  &&
    (memcmp(&buf[byte_count+1], dtls12_version, 2) == 0)) {
      unsigned char content_type = buf[byte_count];
      unsigned char message_type;
      u32 record_length = read_bytes_to_uint32(buf, byte_count+11, 2);

      // the record length exceeds buffer boundaries (not expected)
      if (buf_size - byte_count - 13 - record_length < 0) {
        message_type = MALFORMED_MESSAGE_TYPE;
      }
      else {
        switch(content_type) {
          case HS_CONTENT_TYPE: ;
            unsigned char hs_msg_type = buf[byte_count+13];
            // the minimum size of a correct DTLS 1.2 handshake message is 12 bytes comprising fragment header fields
            if (record_length >= 12) {
              u32 frag_length = read_bytes_to_uint32(buf, byte_count+22, 3);
              // we can check if the handshake record is encrypted by subtracting fragment length from record length
              // which should yield 12 if the fragment is not encrypted
              // the likelyhood for an encrypted fragment to satisfy this condition is very small
              if (record_length - frag_length == 12) {
                // not encrypted
                message_type = hs_msg_type;
              } else {
                // encrypted handshake message
                message_type = UNKNOWN_MESSAGE_TYPE;
              }
            } else {
                // malformed handshake message
                message_type = MALFORMED_MESSAGE_TYPE;
            }
          break;
          case CCS_CONTENT_TYPE:
            if (record_length == 1) {
              // unencrypted CCS
              unsigned char ccs_msg_type = buf[byte_count+13];
              message_type = ccs_msg_type;
            } else {
              if (record_length > 1) {
                // encrypted CCS
                message_type = UNKNOWN_MESSAGE_TYPE;
              } else {
                // malformed CCS
                message_type = MALFORMED_MESSAGE_TYPE;
              }
            }
          break;
          case ALERT_CONTENT_TYPE:
            if (record_length == 2) {
              // unencrypted alert, the type is sufficient for determining which alert occurred
              // unsigned char level = buf[byte_count+13];
              unsigned char type = buf[byte_count+14];
              message_type = type;
            } else {
              if (record_length > 2) {
                // encrypted alert
                message_type = UNKNOWN_MESSAGE_TYPE;
              } else {
                // malformed alert
                message_type = MALFORMED_MESSAGE_TYPE;
              }
            }
          break;
          case APPLICATION_CONTENT_TYPE:
            // for application messages we cannot determine whether they are encrypted or not
            message_type = UNKNOWN_MESSAGE_TYPE;
          break;
          case HEARTBEAT_CONTENT_TYPE:
            // a heartbeat message is at least 3 bytes long (1 byte type, 2 bytes payload length)
            // unfortunately, telling an encrypted message from an unencrypted message cannot be done reliably due to the variable length of padding
            // hence we just use unknown for either case
            if (record_length >= 3) {
              // unsigned char hb_msg_type = buf[byte_count+13];
              // u32 hb_length = read_bytes_to_uint32(buf, byte_count+14, 2);
              // unkown heartbeat message
              message_type = UNKNOWN_MESSAGE_TYPE;
            } else {
              // malformed heartbeat
              message_type = MALFORMED_MESSAGE_TYPE;
            }
          break;
          default:
            // unknown content and message type, should not be hit
            content_type = UNKNOWN_CONTENT_TYPE;
            message_type = UNKNOWN_MESSAGE_TYPE;
          break;
        }
      }

      status_code = (content_type << 8) + message_type;

      status_code = get_mapped_message_code(status_code);
      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = status_code;
      byte_count += record_length;
    } else {
      // we shouldn't really be reaching this code
      byte_count ++;
    }
  }

  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_rtsp(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  char terminator[2] = {0x0D, 0x0A};
  char rtsp[5] = {0x52, 0x54, 0x53, 0x50, 0x2f};

  mem=(char *)ck_alloc(mem_size);

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {
    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the last two bytes are 0x0D0A
    if ((mem_count > 0) && (memcmp(&mem[mem_count - 1], terminator, 2) == 0)) {
      if ((mem_count >= 5) && (memcmp(mem, rtsp, 5) == 0)) {
        //Extract the response code which is the first 3 bytes
        char temp[4];
        memcpy(temp, &mem[9], 4);
        temp[3] = 0x0;
        unsigned int message_code = (unsigned int) atoi(temp);

        if (message_code == 0) break;

        message_code = get_mapped_message_code(message_code);

        state_count++;
        state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
        state_sequence[state_count - 1] = message_code;
        mem_count = 0;
      } else {
        mem_count = 0;
      }
    } else {
      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_ftp(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  char terminator[2] = {0x0D, 0x0A};

  mem=(char *)ck_alloc(mem_size);

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {
    memcpy(&mem[mem_count], buf + byte_count++, 1);
    if ((mem_count > 0) && (memcmp(&mem[mem_count - 1], terminator, 2) == 0) && ((mem[3]==' ') || (isdigit(buf[byte_count]) && (memcmp(&mem[0], &buf[byte_count], 3))!=0) || byte_count == buf_size)) {
    // if ((mem_count > 0) && (memcmp(&mem[mem_count - 1], terminator, 2) == 0)) {
      //Extract the response code which is the first 3 bytes
      char temp[4];
      memcpy(temp, mem, 4);
      temp[3] = 0x0;
      unsigned int message_code = (unsigned int) atoi(temp);

      if (message_code == 0) break;

      message_code = get_mapped_message_code(message_code);

      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = message_code;
      mem_count = 0;
    } else {
      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_mqtt(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // One code per broker packet: its first byte (type and flags: 0x30-0x3F
  // PUBLISH, 0x40 PUBACK, 0x90 SUBACK, 0xD0 PINGRESP, ...), except CONNACK,
  // which carries its return / reason code (0x2000 + code) so a refused
  // connection is a state of its own. Stops at a truncated or malformed
  // packet.
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0, i = 0;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (i < buf_size) {
    unsigned int code, hdrlen, plen = mqtt_packet_len(buf + i, buf_size - i, &hdrlen);
    if (!plen || buf[i] == 0) break;
    code = buf[i];
    if ((buf[i] & 0xF0) == 0x20 && plen >= hdrlen + 2) code = 0x2000 + buf[i + hdrlen + 1];
    state_count++;
    state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
    state_sequence[state_count - 1] = code;
    i += plen;
  }

  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_sip(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  char terminator[2] = {0x0D, 0x0A};
  char sip[4] = {0x53, 0x49, 0x50, 0x2f};

  mem=(char *)ck_alloc(mem_size);

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {
    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the last two bytes are 0x0D0A
    if ((mem_count > 0) && (memcmp(&mem[mem_count - 1], terminator, 2) == 0)) {
      if ((mem_count >= 4) && (memcmp(mem, sip, 4) == 0)) {
        //Extract the response code which is the first 3 bytes
        char temp[4];
        memcpy(temp, &mem[8], 4);
        temp[3] = 0x0;
        unsigned int message_code = (unsigned int) atoi(temp);

        if (message_code == 0) break;

        message_code = get_mapped_message_code(message_code);

        state_count++;
        state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
        state_sequence[state_count - 1] = message_code;
        mem_count = 0;
      } else {
        mem_count = 0;
      }
    } else {
      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_http(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  char terminator[2] = {0x0D, 0x0A};
  char http[5] = {0x48, 0x54, 0x54, 0x50, 0x2f};

  mem=(char *)ck_alloc(mem_size);

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {
    memcpy(&mem[mem_count], buf + byte_count++, 1);

    //Check if the last two bytes are 0x0D0A
    if ((mem_count > 0) && (memcmp(&mem[mem_count - 1], terminator, 2) == 0)) {
      if ((mem_count >= 5) && (memcmp(mem, http, 5) == 0)) {
        //Extract the response code which is the first 3 bytes
        char temp[4];
        memcpy(temp, &mem[9], 4);
        temp[3] = 0x0;
        unsigned int message_code = (unsigned int) atoi(temp);

        if (message_code == 0) break;

        message_code = get_mapped_message_code(message_code);

        state_count++;
        state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
        state_sequence[state_count - 1] = message_code;
        mem_count = 0;
      } else {
        mem_count = 0;
      }
    } else {
      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }
  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}

unsigned int* extract_response_codes_ipp(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  char *mem;
  unsigned int byte_count = 0;
  unsigned int mem_count = 0;
  unsigned int mem_size = 1024;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  char terminatorHTTP[4] = {0x0D, 0x0A, 0x0D, 0x0A};
  char http[5] = {0x48, 0x54, 0x54, 0x50, 0x2F};
  unsigned int message_code = 0;
  char tempHTTP[4];

  mem = (char *)ck_alloc(mem_size);

  //Initial state
  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  if (state_sequence == NULL) PFATAL("Unable realloc a memory region to store state sequence");
  state_sequence[state_count - 1] = 0;

  while (byte_count < buf_size) {
    memcpy(&mem[mem_count], buf + byte_count++, 1);
    //Check if the last two bytes are 0x0D0A0D0A
    if ((mem_count > 3) && (memcmp(&mem[mem_count - 3], terminatorHTTP, 4) == 0)) {
      if ((mem_count >= 5) && (memcmp(mem, http, 5) == 0)) {
        
        memcpy(tempHTTP, &mem[9], 4);
        tempHTTP[3] = 0x0;
        message_code = (unsigned int) atoi(tempHTTP);

        if (message_code == 0) break;
        
        if (message_code == 200) {
          //Extract IPP response code (bytes 3 and 4)
          unsigned int third = (unsigned int) buf[byte_count + 2];
          unsigned int fourth = (unsigned int) buf[byte_count + 3];

          //200 + IPP code to not confuse initial 0 state with successful-ok 0 state
          message_code += (unsigned int) (10 * third + fourth);
        }

        message_code = get_mapped_message_code(message_code);

        state_count++;
        state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));

        if (state_sequence == NULL) PFATAL("Unable realloc a memory region to store state sequence");
        
        state_sequence[state_count - 1] = message_code;       

        mem_count = 0;
      } else {
        mem_count = 0;
      }

    } else {

      mem_count++;
      if (mem_count == mem_size) {
        //enlarge the mem buffer
        mem_size = mem_size * 2;
        mem=(char *)ck_realloc(mem, mem_size);
      }
    }
  }

  if (mem) ck_free(mem);
  *state_count_ref = state_count;
  return state_sequence;
}

// Append one mapped response code to the growing state sequence.
static void resp_append_code(unsigned int code, unsigned int **state_sequence_ref, unsigned int *state_count_ref) {
  *state_count_ref = *state_count_ref + 1;
  *state_sequence_ref = (unsigned int *)ck_realloc(*state_sequence_ref, *state_count_ref * sizeof(unsigned int));
  if (*state_sequence_ref == NULL) PFATAL("Unable to realloc a memory region to store the state sequence");
  (*state_sequence_ref)[*state_count_ref - 1] = code;
}

static unsigned int resp_walk_reply(unsigned char* buf, unsigned int buf_size, unsigned int offset, unsigned int depth, unsigned int **state_sequence_ref, unsigned int *state_count_ref) {
  int number = 0;
  unsigned int off = offset;

  if (depth > 32) return 0; // nesting sanity cap
  if (off >= buf_size) return 0;

  switch (buf[off]) {
    case '+': {
      // Simple string, e.g. +OK, +PONG, +QUEUED
      unsigned int i;
      unsigned int code = 103; // other simple strings
      for (i = off + 1; i < buf_size; i++) {
        if (buf[i] == 0x0D) {
          if ((i + 1 >= buf_size) || (buf[i + 1] != 0x0A)) return 0;
          if ((i - off == 3) && !memcmp(buf + off + 1, "OK", 2)) code = 100;
          else if ((i - off == 5) && !memcmp(buf + off + 1, "PONG", 4)) code = 101;
          else if ((i - off == 7) && !memcmp(buf + off + 1, "QUEUED", 6)) code = 102;
          resp_append_code(code, state_sequence_ref, state_count_ref);
          return i + 2;
        }
      }
      return 0; // unterminated line
    }
    case '-': {
      // Error reply, e.g. -ERR, -WRONGTYPE, -NOAUTH, -WRONGPASS, -MOVED.
      // The code distinguishes the common error keywords.
      unsigned int i;
      unsigned int code = 299; // other errors
      for (i = off + 1; i < buf_size; i++) {
        if (buf[i] == 0x0D) {
          unsigned int wlen;
          unsigned int wend;
          if ((i + 1 >= buf_size) || (buf[i + 1] != 0x0A)) return 0;
          // the keyword is the first word only -- error messages usually
          // carry free text after it (e.g. "-ERR unknown command 'x'")
          wend = off + 1;
          while ((wend < i) && (buf[wend] != ' ')) wend++;
          wlen = wend - (off + 1);
          if ((wlen == 3) && !memcmp(buf + off + 1, "ERR", 3)) code = 200;
          else if ((wlen == 9) && !memcmp(buf + off + 1, "WRONGTYPE", 9)) code = 201;
          else if ((wlen == 6) && !memcmp(buf + off + 1, "NOAUTH", 6)) code = 202;
          else if ((wlen == 9) && !memcmp(buf + off + 1, "WRONGPASS", 9)) code = 203;
          else if ((wlen == 5) && !memcmp(buf + off + 1, "MOVED", 5)) code = 204;
          resp_append_code(code, state_sequence_ref, state_count_ref);
          return i + 2;
        }
      }
      return 0; // unterminated line
    }
    case ':': {
      // Integer reply -- the value itself is not part of the code
      if (!read_resp_number(buf, buf_size, off + 1, &number, &off)) return 0;
      resp_append_code(300, state_sequence_ref, state_count_ref);
      return off;
    }
    case '$': {
      // Bulk string: "$len\r\n<data>\r\n"; "$-1\r\n" is the null bulk string
      if (!read_resp_number(buf, buf_size, off + 1, &number, &off)) return 0;
      if (number == -1) {
        resp_append_code(401, state_sequence_ref, state_count_ref);
        return off;
      }
      if (number < 0) return 0;
      if ((unsigned int)number > buf_size - off) return 0; // data overruns the buffer
      off += number;
      if ((off + 1 >= buf_size) || (buf[off] != 0x0D) || (buf[off + 1] != 0x0A)) return 0;
      off += 2;
      resp_append_code(400, state_sequence_ref, state_count_ref);
      return off;
    }
    case '*': {
      // Array of replies: "*N\r\n" followed by N replies; "*-1\r\n" is the
      // null array. The array gets its own code, then each child reply.
      unsigned int i;
      if (!read_resp_number(buf, buf_size, off + 1, &number, &off)) return 0;
      if (number == -1) {
        resp_append_code(501, state_sequence_ref, state_count_ref);
        return off;
      }
      if (number < 0) return 0;
      resp_append_code(500, state_sequence_ref, state_count_ref);
      for (i = 0; i < (unsigned int)number; i++) {
        off = resp_walk_reply(buf, buf_size, off, depth + 1, state_sequence_ref, state_count_ref);
        if (off == 0) return 0;
      }
      return off;
    }
    // RESP3 (after HELLO 3)
    case '_': {
      // Null: "_\r\n"
      if ((off + 2 >= buf_size) || (buf[off + 1] != 0x0D) || (buf[off + 2] != 0x0A)) return 0;
      resp_append_code(600, state_sequence_ref, state_count_ref);
      return off + 3;
    }
    case ',':   // double
    case '#':   // boolean
    case '(': { // big number
      unsigned int i;
      for (i = off + 1; i < buf_size; i++) {
        if (buf[i] == 0x0D) {
          if ((i + 1 >= buf_size) || (buf[i + 1] != 0x0A)) return 0;
          resp_append_code(buf[off] == ',' ? 601 : buf[off] == '#' ? 602 : 603,
                           state_sequence_ref, state_count_ref);
          return i + 2;
        }
      }
      return 0; // unterminated line
    }
    case '!':   // blob error
    case '=': { // verbatim string
      unsigned int code = (buf[off] == '!') ? 604 : 605;
      if (!read_resp_number(buf, buf_size, off + 1, &number, &off)) return 0;
      if (number < 0) return 0;
      if ((unsigned int)number > buf_size - off) return 0; // data overruns the buffer
      off += number;
      if ((off + 1 >= buf_size) || (buf[off] != 0x0D) || (buf[off + 1] != 0x0A)) return 0;
      resp_append_code(code, state_sequence_ref, state_count_ref);
      return off + 2;
    }
    case '%':   // map: N key/value pairs
    case '~':   // set
    case '>':   // push
    case '|': { // attribute: N pairs, then the reply it annotates
      unsigned int i, children;
      unsigned char type = buf[off];
      if (!read_resp_number(buf, buf_size, off + 1, &number, &off)) return 0;
      if (number < 0) return 0;
      children = (type == '%' || type == '|') ? 2 * (unsigned int)number : (unsigned int)number;
      resp_append_code(type == '%' ? 700 : type == '~' ? 701 : type == '>' ? 702 : 703,
                       state_sequence_ref, state_count_ref);
      for (i = 0; i < children; i++) {
        off = resp_walk_reply(buf, buf_size, off, depth + 1, state_sequence_ref, state_count_ref);
        if (off == 0) return 0;
      }
      if (type == '|') return resp_walk_reply(buf, buf_size, off, depth + 1, state_sequence_ref, state_count_ref);
      return off;
    }
    default:
      return 0; // unknown reply type -- stop parsing
  }
}

// RESP (REdis Serialization Protocol) response-code extraction. Codes:
//   +OK=100 +PONG=101 +QUEUED=102 other simple strings=103
//   -ERR=200 -WRONGTYPE=201 -NOAUTH=202 -WRONGPASS=203 -MOVED=204 other errors=299
//   integer=300  bulk=400 null bulk=401  array=500 null array=501
unsigned int* extract_response_codes_resp(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  unsigned int offset = 0;

  //Initial state
  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  if (state_sequence == NULL) PFATAL("Unable to realloc a memory region to store the state sequence");
  state_sequence[state_count - 1] = 0;

  while (offset < buf_size) {
    offset = resp_walk_reply(buf, buf_size, offset, 0, &state_sequence, &state_count);
    if (offset == 0) break; // malformed reply -- keep what was parsed
  }

  *state_count_ref = state_count;
  return state_sequence;
}

// kl_messages manipulating functions

klist_t(lms) *construct_kl_messages(u8* fname, region_t *regions, u32 region_count)
{
  FILE *fseed = NULL;
  fseed = fopen(fname, "rb");
  if (fseed == NULL) PFATAL("Cannot open seed file %s", fname);

  klist_t(lms) *kl_messages = kl_init(lms);
  u32 i;

  for (i = 0; i < region_count; i++) {
    //Identify region size
    u32 len = regions[i].end_byte - regions[i].start_byte + 1;

    //Create a new message
    message_t *m = (message_t *) ck_alloc(sizeof(message_t));
    m->mdata = (char *) ck_alloc(len);
    m->msize = len;
    if (m->mdata == NULL) PFATAL("Unable to allocate memory region to store new message");
    fread(m->mdata, 1, len, fseed);

    //Insert the message to the linked list
    *kl_pushp(lms, kl_messages) = m;
  }

  if (fseed != NULL) fclose(fseed);
  return kl_messages;
}

void delete_kl_messages(klist_t(lms) *kl_messages)
{
  /* Free all messages in the list before destroying the list itself */
  message_t *m;

  int ret = kl_shift(lms, kl_messages, &m);
  while (ret == 0) {
    if (m) {
      ck_free(m->mdata);
      ck_free(m);
    }
    ret = kl_shift(lms, kl_messages, &m);
  }

  /* Finally, destroy the list */
	kl_destroy(lms, kl_messages);
}

kliter_t(lms) *get_last_message(klist_t(lms) *kl_messages)
{
  kliter_t(lms) *it;
  it = kl_begin(kl_messages);
  while (kl_next(it) != kl_end(kl_messages)) {
    it = kl_next(it);
  }
  return it;
}


u32 save_kl_messages_to_file(klist_t(lms) *kl_messages, u8 *fname, u8 replay_enabled, u32 max_count)
{
  u8 *mem = NULL;
  u32 len = 0, message_size = 0;
  kliter_t(lms) *it;

  s32 fd = open(fname, O_WRONLY | O_CREAT, 0600);
  if (fd < 0) PFATAL("Unable to create file '%s'", fname);

  u32 message_count = 0;
  //Iterate through all messages in the linked list
  for (it = kl_begin(kl_messages); it != kl_end(kl_messages) && message_count < max_count; it = kl_next(it)) {
    message_size = kl_val(it)->msize;
    if (replay_enabled) {
		  mem = (u8 *)ck_realloc(mem, 4 + len + message_size);

      //Save packet size first
      u32 *psize = (u32*)&mem[len];
      *psize = message_size;

      //Save packet content
      memcpy(&mem[len + 4], kl_val(it)->mdata, message_size);
      len = 4 + len + message_size;
    } else {
      mem = (u8 *)ck_realloc(mem, len + message_size);

      //Save packet content
      memcpy(&mem[len], kl_val(it)->mdata, message_size);
      len = len + message_size;
    }
    message_count++;
  }

  //Write everything to file & close the file
  ck_write(fd, mem, len, fname);
  close(fd);

  //Free the temporary buffer
  ck_free(mem);

  return len;
}

region_t* convert_kl_messages_to_regions(klist_t(lms) *kl_messages, u32* region_count_ref, u32 max_count)
{
  region_t *regions = NULL;
  kliter_t(lms) *it;

  u32 region_count = 1;
  s32 cur_start = 0, cur_end = 0;
  //Iterate through all messages in the linked list
  for (it = kl_begin(kl_messages); it != kl_end(kl_messages) && region_count <= max_count ; it = kl_next(it)) {
    regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));

    cur_end = cur_start + kl_val(it)->msize - 1;
    if (cur_end < 0) PFATAL("End_byte cannot be negative");

    regions[region_count - 1].start_byte = cur_start;
    regions[region_count - 1].end_byte = cur_end;
    regions[region_count - 1].state_sequence = NULL;
    regions[region_count - 1].state_count = 0;

    cur_start = cur_end + 1;
    region_count++;
  }

  *region_count_ref = region_count - 1;
  return regions;
}

// Network communication functions

int net_send(int sockfd, struct timeval timeout, char *mem, unsigned int len) {
  unsigned int byte_count = 0;
  int n;
  struct pollfd pfd[1];
  pfd[0].fd = sockfd;
  pfd[0].events = POLLOUT;
  int rv = poll(pfd, 1, 1);

  setsockopt(sockfd, SOL_SOCKET, SO_SNDTIMEO, (char *)&timeout, sizeof(timeout));
  if (rv > 0) {
    if (pfd[0].revents & POLLOUT) {
      while (byte_count < len) {
        usleep(10);
        n = send(sockfd, &mem[byte_count], len - byte_count, MSG_NOSIGNAL);
        if (n == 0) return byte_count;
        if (n == -1) return -1;
        byte_count += n;
      }
    }
  }
  return byte_count;
}

int net_recv(int sockfd, struct timeval timeout, int poll_w, char **response_buf, unsigned int *len) {
  char temp_buf[1000];
  int n;
  struct pollfd pfd[1];
  pfd[0].fd = sockfd;
  pfd[0].events = POLLIN;
  int rv = poll(pfd, 1, poll_w);

  setsockopt(sockfd, SOL_SOCKET, SO_RCVTIMEO, (char *)&timeout, sizeof(timeout));
  // data received
  if (rv > 0) {
    if (pfd[0].revents & POLLIN) {
      n = recv(sockfd, temp_buf, sizeof(temp_buf), 0);
      if ((n < 0) && (errno != EAGAIN)) {
        return 1;
      }
      while (n > 0) {
        usleep(10);
        *response_buf = (unsigned char *)ck_realloc(*response_buf, *len + n + 1);
        memcpy(&(*response_buf)[*len], temp_buf, n);
        (*response_buf)[(*len) + n] = '\0';
        *len = *len + n;
        n = recv(sockfd, temp_buf, sizeof(temp_buf), 0);
        if ((n < 0) && (errno != EAGAIN)) {
          return 1;
        }
      }
    }
  } else
    if (rv < 0) // an error was returned
      return 1;

  // rv == 0 poll timeout or all data pending after poll has been received successfully
  return 0;
}

// Utility function

void save_regions_to_file(region_t *regions, unsigned int region_count, unsigned char *fname)
{
  int fd;
  FILE* fp;

  fd = open(fname, O_WRONLY | O_CREAT | O_EXCL, 0600);

  if (fd < 0) return;

  fp = fdopen(fd, "w");

  if (!fp) {
    close(fd);
    return;
  }

  int i;

  for(i=0; i < region_count; i++) {
     fprintf(fp, "Region %d - Start: %d, End: %d\n", i, regions[i].start_byte, regions[i].end_byte);
  }

  fclose(fp);
}

int str_split(char* a_str, const char* a_delim, char **result, int a_count)
{
	char *token;
	int count = 0;

	/* count number of tokens */
	/* get the first token */
	char* tmp1 = strdup(a_str);
	token = strtok(tmp1, a_delim);

	/* walk through other tokens */
	while (token != NULL)
	{
		count++;
		token = strtok(NULL, a_delim);
	}

	if (count != a_count)
	{
		return 1;
	}

	/* split input string, store tokens into result */
	count = 0;
	/* get the first token */
	token = strtok(a_str, a_delim);

	/* walk through other tokens */

	while (token != NULL)
	{
		result[count] = token;
		count++;
		token = strtok(NULL, a_delim);
	}

	free(tmp1);
	return 0;
}

void str_rtrim(char* a_str)
{
	char* ptr = a_str;
	int count = 0;
	while ((*ptr != '\n') && (*ptr != '\t') && (*ptr != ' ') && (count < strlen(a_str))) {
		ptr++;
		count++;
	}
	if (count < strlen(a_str)) {
		*ptr = '\0';
	}
}

int parse_net_config(u8* net_config, u8* protocol, u8** ip_address, u32* port)
{
  char  buf[80];
  char **tokens;
  int tokenCount = 3;

  tokens = (char**)malloc(sizeof(char*) * (tokenCount));

  if (strlen(net_config) > 80) return 1;

  strncpy(buf, net_config, strlen(net_config));
   str_rtrim(buf);

  if (!str_split(buf, "/", tokens, tokenCount))
  {
      if (!strcmp(tokens[0], "tcp:")) {
        *protocol = PRO_TCP;
      } else if (!strcmp(tokens[0], "udp:")) {
        *protocol = PRO_UDP;
      } else return 1;

      //TODO: check the format of this IP address
      *ip_address = strdup(tokens[1]);

      *port = atoi(tokens[2]);
      if (*port == 0) return 1;
  } else return 1;
  free(tokens);
  return 0;
}

u8* state_sequence_to_string(unsigned int *stateSequence, unsigned int stateCount) {
  u32 i = 0;

  u8 *out = NULL;

  char strState[STATE_STR_LEN];
  size_t len = 0;
  for (i = 0; i < stateCount; i++) {
    //Limit the loop to shorten the output string
    if ((i >= 2) && (stateSequence[i] == stateSequence[i - 1]) && (stateSequence[i] == stateSequence[i - 2])) continue;
    unsigned int stateID = stateSequence[i];
    if (i == stateCount - 1) {
      snprintf(strState, STATE_STR_LEN, "%d", (int) stateID);
    } else {
      snprintf(strState, STATE_STR_LEN, "%d-", (int) stateID);
    }
    out = (u8 *)ck_realloc(out, len + strlen(strState) + 1);
    memcpy(&out[len], strState, strlen(strState) + 1);
    len=strlen(out);
    //As Linux limit the size of the file name
    //we set a fixed upper bound here
    if (len > 150 && (i + 1 < stateCount)) {
      snprintf(strState, STATE_STR_LEN, "%s", "end-at-");
      out = (u8 *)ck_realloc(out, len + strlen(strState) + 1);
      memcpy(&out[len], strState, strlen(strState) + 1);
      len=strlen(out);

      snprintf(strState, STATE_STR_LEN, "%d", (int) stateSequence[stateCount - 1]);
      out = (u8 *)ck_realloc(out, len + strlen(strState) + 1);
      memcpy(&out[len], strState, strlen(strState) + 1);
      len=strlen(out);
      break;
    }
  }
  return out;
}


void hexdump(unsigned char *msg, unsigned char * buf, int start, int end) {
  printf("%s : ", msg);
  for (int i=start; i<=end; i++) {
    printf("%02x", buf[i]);
  }
  printf("\n");
}


u32 read_bytes_to_uint32(unsigned char* buf, unsigned int offset, int num_bytes) {
  u32 val = 0;
  for (int i=0; i<num_bytes; i++) {
    val = (val << 8) + buf[i+offset];
  }
  return val;
}

region_t* extract_requests_memcached(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  unsigned int byte_count = 0;
  unsigned int region_count = 0;
  region_t *regions = NULL;
  unsigned int cur_start = 0;

  while (byte_count < buf_size) {
    // memcached's text protocol is line based: every LF terminates one
    // request line (or the data block of a "set"-family command, which the
    // server consumes as its next line)
    if (buf[byte_count] == '\n') {
      region_count++;
      regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
      regions[region_count - 1].start_byte = cur_start;
      regions[region_count - 1].end_byte = byte_count;
      regions[region_count - 1].state_sequence = NULL;
      regions[region_count - 1].state_count = 0;
      cur_start = byte_count + 1;
    }
    byte_count++;
  }

  if (cur_start < buf_size) { // trailing partial line keeps its own region
    region_count++;
    regions = (region_t *)ck_realloc(regions, region_count * sizeof(region_t));
    regions[region_count - 1].start_byte = cur_start;
    regions[region_count - 1].end_byte = buf_size - 1;
    regions[region_count - 1].state_sequence = NULL;
    regions[region_count - 1].state_count = 0;
  }

  *region_count_ref = region_count;
  return regions;
}

// The numeric value of the index-th space-separated token of a reply line
// (0 if absent; capped so a mutated size cannot overflow).
static unsigned int memcached_token_number(const unsigned char* line, unsigned int len, unsigned int index)
{
  unsigned int p = 0, value = 0;
  while (index--) {
    while (p < len && line[p] != ' ') p++;
    while (p < len && line[p] == ' ') p++;
  }
  while (p < len && line[p] >= '0' && line[p] <= '9' && value < 0x10000000)
    value = value * 10 + (line[p++] - '0');
  return value;
}

// Classify one reply line (CR/LF stripped) by its first token, text and
// meta protocol alike. "VALUE <key> <flags> <bytes>" and "VA <bytes>"
// announce a data block of that many bytes plus CRLF: *data_len.
static unsigned int memcached_line_code(const unsigned char* line, unsigned int len, unsigned int* data_len)
{
  unsigned int tlen = 0, q;
  *data_len = 0;
  while (tlen < len && line[tlen] != ' ') tlen++;
  if (tlen == 0) return 0; // empty line carries no state
#define MEMC_TOK(s) (tlen == (unsigned int)(sizeof(s) - 1) && !memcmp(line, s, sizeof(s) - 1))
  if (MEMC_TOK("STORED"))       return 1;
  if (MEMC_TOK("DELETED"))      return 2;
  if (MEMC_TOK("VALUE"))        { *data_len = memcached_token_number(line, len, 3); return 3; }
  if (MEMC_TOK("END"))          return 4;
  if (MEMC_TOK("STAT"))         return 5;
  if (MEMC_TOK("OK"))           return 6;
  if (MEMC_TOK("TOUCHED"))      return 7;
  if (MEMC_TOK("VERSION"))      return 8;
  if (MEMC_TOK("ERROR"))        return 9;
  if (MEMC_TOK("CLIENT_ERROR")) return 10;
  if (MEMC_TOK("SERVER_ERROR")) return 11;
  if (MEMC_TOK("NOT_FOUND"))    return 12;
  if (MEMC_TOK("NOT_STORED"))   return 13;
  if (MEMC_TOK("EXISTS"))       return 14;
  // meta protocol (mg/ms/md/ma/mn)
  if (MEMC_TOK("HD"))           return 16;
  if (MEMC_TOK("VA"))           { *data_len = memcached_token_number(line, len, 1); return 17; }
  if (MEMC_TOK("EN"))           return 18;
  if (MEMC_TOK("NF"))           return 19;
  if (MEMC_TOK("NS"))           return 20;
  if (MEMC_TOK("EX"))           return 21;
  if (MEMC_TOK("MN"))           return 22;
  if (MEMC_TOK("RESET"))        return 23;
  if (MEMC_TOK("BUSY"))         return 25;
  if (MEMC_TOK("BADCLASS"))     return 26;
#undef MEMC_TOK
  for (q = 0; q < tlen && line[q] >= '0' && line[q] <= '9'; q++);
  if (q == tlen) return 24; // incr/decr result
  return 15;                // other non-empty line
}

unsigned int* extract_response_codes_memcached(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  unsigned int i = 0;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0; // initial status code is 0

  while (i < buf_size) {
    unsigned int j = i, len, code, data_len;
    while (j < buf_size && buf[j] != '\n') j++;
    if (j == buf_size) break; // partial line: wait for its LF
    len = j - i;
    if (len > 0 && buf[i + len - 1] == '\r') len--;
    code = memcached_line_code(buf + i, len, &data_len);
    if (code != 0) {
      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = code;
    }
    i = j + 1;
    if (data_len) { // skip the data block and its CRLF
      if (data_len > buf_size - i || data_len + 2 > buf_size - i) break;
      i += data_len + 2;
    }
  }

  *state_count_ref = state_count;
  return state_sequence;
}

// NTP packet sizes: the 48-byte header alone, with a 4-byte key ID, or
// with a key ID and a 16-byte (MD5) or 20-byte (SHA1) digest.
static const unsigned int ntp_packet_sizes[4] = {48, 52, 68, 72};

// A plausible first byte of a client packet: nonzero version (the seeds
// probe versions up to 5) and nonzero mode.
static int ntp_request_start(unsigned char b)
{
  return ((b >> 3) & 7) != 0 && (b & 7) != 0;
}

// A server reply's first byte: leap indicator 0, mode 4 (server).
static int ntp_reply_start(unsigned char b)
{
  return (b & 0xC7) == 0x04;
}

// The size of the packet at b: the shortest of ntp_packet_sizes after
// which the buffer ends or the next packet plausibly starts; 0 if none.
static unsigned int ntp_packet_len(const unsigned char* b, unsigned int rem, int reply)
{
  unsigned int k;
  for (k = 0; k < 4; k++) {
    unsigned int len = ntp_packet_sizes[k];
    if (len == rem) return len;
    if (len < rem && (reply ? ntp_reply_start(b[len]) : ntp_request_start(b[len]))) return len;
  }
  return 0;
}

region_t* extract_requests_chrony(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  // NTP over UDP: one region per packet, each sent as one datagram. A
  // packet is 48, 52, 68 or 72 bytes (ntp_packet_len); when no size lines
  // up with a plausible next packet, a remainder of at most 72 bytes is one
  // packet and a longer one splits after 48. A short tail is its own
  // region. The old whole-file-as-one-region design sent the concatenated
  // seed as one datagram that chronyd silently dropped.
  region_t *regions = NULL;
  unsigned int region_count = 0;
  unsigned int i = 0;

  while (i < buf_size) {
    unsigned int rem = buf_size - i, len = ntp_packet_len(buf + i, rem, 0);
    if (!len) len = (rem > 72) ? 48 : rem;
    unsigned int end = i + len;
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = end - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    i = end;
  }

  *region_count_ref = region_count;
  return regions;
}

unsigned int* extract_response_codes_chrony(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // NTP server reply: byte0 = LI(2b)|VN(2b)|Mode(4b) with Mode=4, LI=0 --
  // 0x1c for VN3 clients, 0x24 for VN4. chronyd answers in the client's own
  // version, so match on the mode nibble, not one byte value: the original
  // 0x24-only split missed every VN3 reply (the seeds are VN3), the state
  // sequence stayed [0], zero transitions were ever recorded, and afl-fuzz
  // PFATALed with "states hashtable ... initial state" on seed 1.
  // byte1 carries the stratum; map (stratum, VN/LI bits) to a state code.
  unsigned int byte_count = 0;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0; // initial status code is 0

  while (byte_count + 2 <= buf_size) {
    if (ntp_reply_start(buf[byte_count])) {
      unsigned int code = 1 + ((buf[byte_count + 1] & 0x0f) << 2) + ((buf[byte_count] >> 5) & 0x03);
      unsigned int len = ntp_packet_len(buf + byte_count, buf_size - byte_count, 1);
      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = code;
      // skip the reply body and its key ID / MAC; a stray reply-like byte
      // inside timestamps or a digest is not a new reply
      byte_count += len ? len : 48;
    } else {
      byte_count++;
    }
  }

  *state_count_ref = state_count;
  return state_sequence;
}



region_t* extract_requests_chronyc(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  // chrony CANDM command protocol (cmdmon, UDP): each request is one
  // datagram with header 06 01 00 00 | command(u16 BE) | attempt(u16 BE)
  // | sequence(u32 BE) | body. Split at the next header magic (06 01 00 00);
  // a tail that does not parse becomes one final region so nothing is lost.
  // Deterministic scan: same bytes -> same regions on every run.
  region_t *regions = NULL;
  unsigned int region_count = 0;
  unsigned int i = 0;

  while (i < buf_size) {
    unsigned int j;
    int hdr = (buf[i] == 0x06 && i + 4 <= buf_size && buf[i + 1] == 0x01 &&
               buf[i + 2] == 0 && buf[i + 3] == 0);
    if (hdr) {
      j = i + 12; // smallest sensible request: 12-byte header + body
      while (j + 4 <= buf_size) {
        if (buf[j] == 0x06 && buf[j + 1] == 0x01 && buf[j + 2] == 0 && buf[j + 3] == 0) break;
        j++;
      }
      // no further header: this request runs to the end of the buffer
      if (j + 4 > buf_size) j = buf_size;
    } else {
      j = buf_size; // unparsable remainder: one region
    }
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = j - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    i = j;
    if (!hdr) break;
  }

  *region_count_ref = region_count;
  return regions;
}

unsigned int* extract_response_codes_chronyc(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // Response: 06 02 00 00 | command(u16 BE) | reply(u16 BE) | status(u16 BE)
  // | ... State code = 0x10000 + (command << 8) + status (low bytes), so a
  // refused command (STT_UNAUTH, STT_BADPKTLENGTH, ...) is its own state.
  // Body multi-record sections may contain accidental header matches;
  // they only add (deterministic) states, never remove any.
  unsigned int byte_count = 0;
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0; // initial state

  while (byte_count + 12 <= buf_size) {
    if (buf[byte_count] == 0x06 && buf[byte_count + 1] == 0x02 &&
        buf[byte_count + 2] == 0 && buf[byte_count + 3] == 0) {
      unsigned int cmd = buf[byte_count + 5], status = buf[byte_count + 9];
      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = 0x10000 + (cmd << 8) + status;
      byte_count += 12;
    } else {
      byte_count++;
    }
  }

  *state_count_ref = state_count;
  return state_sequence;
}

// CoAP over TCP (RFC 8323), the transport the libcoap cell fuzzes: byte 0
// is Len(4 bits) | TKL(4 bits); Len 13/14/15 adds 1/2/4 extended-length
// bytes (+13/+269/+65805); then the Code byte; TKL 13/14 (RFC 8974) adds
// 1/2 extended token-length bytes (+13/+269); then the token, then Len
// bytes of options and payload. Returns the message length, or 0 when
// the buffer does not hold one complete message; *code_off receives the
// offset of the Code byte.
static unsigned int coap_tcp_message_len(const unsigned char* b, unsigned int rem, unsigned int* code_off)
{
  unsigned long long len = b[0] >> 4, tkl = b[0] & 0x0f, total;
  unsigned int p = 1, k, ext;
  if (rem < 2 || tkl == 15) return 0;
  ext = (len == 13) ? 1 : (len == 14) ? 2 : (len == 15) ? 4 : 0;
  if (rem < 1 + ext + 1) return 0;
  if (ext) {
    unsigned long long v = 0;
    for (k = 0; k < ext; k++) v = (v << 8) | b[p + k];
    len = v + (ext == 1 ? 13 : ext == 2 ? 269 : 65805);
    p += ext;
  }
  *code_off = p++;
  if (tkl >= 13) {
    unsigned int text = (tkl == 13) ? 1 : 2;
    if (rem < p + text) return 0;
    tkl = (text == 1) ? 13 + b[p] : 269 + (((unsigned int)b[p] << 8) | b[p + 1]);
    p += text;
  }
  total = p + tkl + len;
  if (total > rem) return 0;
  return (unsigned int)total;
}

region_t* extract_requests_coap(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  // One region per RFC 8323 message; a tail that does not frame becomes
  // one final region, so the regions always cover the whole buffer.
  region_t *regions = NULL;
  unsigned int region_count = 0, i = 0;

  while (i < buf_size) {
    unsigned int code_off, mlen = coap_tcp_message_len(buf + i, buf_size - i, &code_off);
    int framed = (mlen != 0);
    if (!framed) mlen = buf_size - i;
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = i + mlen - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    i += mlen;
    if (!framed) break;
  }

  *region_count_ref = region_count;
  return regions;
}

unsigned int* extract_response_codes_coap(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // One code per RFC 8323 message: its Code byte (0x45 = 2.05 Content,
  // 0x84 = 4.04 Not Found, 0xE1 = 7.01 CSM, 0xE3 = 7.03 Pong, ...); empty
  // messages (code 0) carry no state. Stops at a message that does not
  // frame.
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0, i = 0;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0; // initial status code is 0

  while (i < buf_size) {
    unsigned int code_off, mlen = coap_tcp_message_len(buf + i, buf_size - i, &code_off);
    if (!mlen) break;
    if (buf[i + code_off] != 0) {
      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = buf[i + code_off];
    }
    i += mlen;
  }

  *state_count_ref = state_count;
  return state_sequence;
}


region_t* extract_requests_imap(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  // IMAP is line-based: one tagged command per CRLF-terminated line.
  // Literals ("{N}" + N raw octets) exist but are rare in hand-built seeds;
  // a CRLF split keeps every well-formed command intact and turns
  // literal-carrying mutants into extra (server-rejected) regions.
  region_t *regions = NULL;
  unsigned int region_count = 0;
  unsigned int i = 0, start = 0;

  while (i < buf_size) {
    if (buf[i] == '\n') {
      regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
      regions[region_count].start_byte = start;
      regions[region_count].end_byte = i;
      regions[region_count].state_sequence = NULL;
      regions[region_count].state_count = 0;
      region_count++;
      start = i + 1;
    }
    i++;
  }
  if (start < buf_size) { // trailing partial line keeps its own region
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = start;
    regions[region_count].end_byte = buf_size - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
  }

  *region_count_ref = region_count;
  return regions;
}

// Classify one IMAP response line into a small deterministic state code.
// Untagged:  "* OK/NO/BAD/BYE/PREAUTH", "* CAPABILITY/FLAGS/...", and the
// number-first forms "* <n> FETCH/EXISTS/EXPUNGE/RECENT" (name = token 3).
// Tagged:    "<tag> OK/NO/BAD". Continuation "+" lines get their own code.
static unsigned int imap_line_code(const unsigned char* line, unsigned int len)
{
  unsigned int p = 0, ts, tlen, q;
  int untagged, allnum;

  while (p < len && (line[p] == ' ' || line[p] == '\r' || line[p] == '\n')) p++;
  ts = p;
  while (p < len && line[p] != ' ' && line[p] != '\r' && line[p] != '\n') p++;
  tlen = p - ts;
  if (tlen == 0) return 0; // blank line carries no state
  if (tlen == 1 && line[ts] == '+') return 24; // continuation request
  untagged = (tlen == 1 && line[ts] == '*');

  // token 2
  while (p < len && line[p] == ' ') p++;
  ts = p;
  while (p < len && line[p] != ' ' && line[p] != '\r' && line[p] != '\n') p++;
  tlen = p - ts;
  if (tlen == 0) return untagged ? 6 : 34;

  if (untagged) {
    allnum = 1;
    for (q = ts; q < ts + tlen; q++) {
      if (line[q] < '0' || line[q] > '9') { allnum = 0; break; }
    }
    if (allnum) {
      // "* <n> NAME ..." -- the response name is token 3
      while (p < len && line[p] == ' ') p++;
      ts = p;
      while (p < len && line[p] != ' ' && line[p] != '\r' && line[p] != '\n') p++;
      tlen = p - ts;
      if (tlen == 0) return 6;
    }
  }

#define IMAP_TOK(s) (tlen == (unsigned int)(sizeof(s) - 1) && !strncmp((const char*)line + ts, s, sizeof(s) - 1))
  if (IMAP_TOK("OK"))          return untagged ? 1 : 31;
  if (IMAP_TOK("NO"))          return untagged ? 2 : 32;
  if (IMAP_TOK("BAD"))         return untagged ? 3 : 33;
  if (IMAP_TOK("BYE"))         return 4;
  if (IMAP_TOK("PREAUTH"))     return 5;
  if (IMAP_TOK("CAPABILITY"))  return 7;
  if (IMAP_TOK("FLAGS"))       return 8;
  if (IMAP_TOK("LIST"))        return 9;
  if (IMAP_TOK("LSUB"))        return 10;
  if (IMAP_TOK("SEARCH"))      return 11;
  if (IMAP_TOK("SORT"))        return 12;
  if (IMAP_TOK("STATUS"))      return 13;
  if (IMAP_TOK("FETCH"))       return 14;
  if (IMAP_TOK("EXPUNGE"))     return 15;
  if (IMAP_TOK("EXISTS"))      return 16;
  if (IMAP_TOK("RECENT"))      return 17;
  if (IMAP_TOK("UIDVALIDITY")) return 18;
  if (IMAP_TOK("UIDNEXT"))     return 19;
  if (IMAP_TOK("NAMESPACE"))   return 20;
  if (IMAP_TOK("ENABLE"))      return 21;
  if (IMAP_TOK("ID"))          return 22;
#undef IMAP_TOK
  return untagged ? 23 : 34;
}

// A line (LF excluded) ending in "{N}" or "{N+}" announces N literal octets
// after its LF; returns 1 and sets *n when it does.
static int imap_literal_len(const unsigned char* line, unsigned int len, unsigned int* n)
{
  unsigned int p, s, value = 0;
  if (len && line[len - 1] == '\r') len--;
  if (!len || line[len - 1] != '}') return 0;
  p = len - 1;
  if (p && line[p - 1] == '+') p--;
  s = p;
  while (s && line[s - 1] >= '0' && line[s - 1] <= '9') s--;
  if (s == p || s == 0 || line[s - 1] != '{') return 0;
  for (; s < p; s++) {
    value = value * 10 + (line[s] - '0');
    if (value > 0x0fffffff) value = 0x0fffffff; // runs past any buffer
  }
  *n = value;
  return 1;
}

unsigned int* extract_response_codes_imap(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // One code per response. A response whose line ends in a literal
  // announcement continues after the literal octets (message bodies,
  // headers) up to the next LF, again possibly with a literal: none of
  // that is classified as a line of its own.
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  unsigned int i = 0, code;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0; // initial status code is 0

  while (i < buf_size) {
    unsigned int seg = i, j = i, n;
    while (j < buf_size && buf[j] != '\n') j++;
    // a trailing partial line is classified too
    code = imap_line_code(buf + i, j - i);
    if (code != 0) {
      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = code;
    }
    while (j < buf_size && imap_literal_len(buf + seg, j - seg, &n)) {
      if (n >= buf_size - j) { j = buf_size; break; }
      seg = j + 1 + n;
      j = seg;
      while (j < buf_size && buf[j] != '\n') j++;
    }
    i = j + 1;
  }

  *state_count_ref = state_count;
  return state_sequence;
}


// HTTP/2 over TCP (h2c prior knowledge): the 24-byte client connection
// preface magic ("PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n") is region 0, then
// 9-byte frame headers (3-byte BE length + type + flags + stream id).
// Unparsable tail = one final region.
static const char h2_preface[24] = "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";

region_t* extract_requests_http2(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  region_t *regions = NULL;
  unsigned int region_count = 0, i = 0;
  if (buf_size >= 24 && !memcmp(buf, h2_preface, 24)) {
    regions = (region_t *)ck_realloc(regions, sizeof(region_t));
    regions[0].start_byte = 0; regions[0].end_byte = 23;
    regions[0].state_sequence = NULL; regions[0].state_count = 0;
    region_count = 1; i = 24;
  }
  while (i < buf_size) {
    unsigned int flen, mlen;
    if (buf_size - i < 9) mlen = buf_size - i;
    else {
      flen = ((unsigned int)buf[i] << 16) | ((unsigned int)buf[i+1] << 8) | buf[i+2];
      if (i + 9 + flen > buf_size) mlen = buf_size - i;
      else mlen = 9 + flen;
    }
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = i + mlen - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    i += mlen;
    if (mlen < 9) break;
  }
  *region_count_ref = region_count;
  return regions;
}

unsigned int* extract_response_codes_http2(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // State code = 100 + frame type (0 DATA, 1 HEADERS, 3 RST_STREAM,
  // 4 SETTINGS, 6 PING, 7 GOAWAY, 8 WINDOW_UPDATE, 5 PUSH_PROMISE):
  // the frame-type sequence IS the h2 session state machine. SETTINGS and
  // PING acknowledgements get 200 + type, RST_STREAM and GOAWAY carry
  // their error code (1000 + code, 2000 + code).
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0, i = 0;
  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;
  while (i + 9 <= buf_size) {
    unsigned int flen = ((unsigned int)buf[i] << 16) | ((unsigned int)buf[i+1] << 8) | buf[i+2];
    if (i + 9 + flen > buf_size) break;
    unsigned int type = buf[i+3], code = 100 + type;
    if ((type == 4 || type == 6) && (buf[i+4] & 0x01)) {
      code = 200 + type;  // SETTINGS / PING with the ACK flag
    } else if (type == 3 && flen >= 4) {
      // RST_STREAM: 1000 + error code (unknown codes share 1255)
      unsigned int error = ((unsigned int)buf[i+9] << 24) | ((unsigned int)buf[i+10] << 16) |
                           ((unsigned int)buf[i+11] << 8) | buf[i+12];
      code = 1000 + (error < 0xff ? error : 0xff);
    } else if (type == 7 && flen >= 8) {
      // GOAWAY: 2000 + error code (after the 4-byte last stream id)
      unsigned int error = ((unsigned int)buf[i+13] << 24) | ((unsigned int)buf[i+14] << 16) |
                           ((unsigned int)buf[i+15] << 8) | buf[i+16];
      code = 2000 + (error < 0xff ? error : 0xff);
    }
    state_count++;
    state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
    state_sequence[state_count - 1] = code;
    i += 9 + flen;
  }
  *state_count_ref = state_count;
  return state_sequence;
}


region_t* extract_requests_bgp(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  // BGP packet: 16-byte all-FF marker + 2-byte BE length (incl. header,
  // min 19, max 4096) + 1-byte type. Split on the length field; a tail that
  // does not parse (mutant) becomes one final region so nothing is lost.
  region_t *regions = NULL;
  unsigned int region_count = 0;
  unsigned int i = 0;

  while (i < buf_size) {
    unsigned int plen = 0, j;
    int marker_ok = (buf_size - i >= 19);
    if (marker_ok) {
      for (j = i; j < i + 16; j++) if (buf[j] != 0xFF) { marker_ok = 0; break; }
    }
    if (marker_ok) {
      plen = (buf[i + 16] << 8) | buf[i + 17];
      if (plen < 19 || plen > 4096 || i + plen > buf_size) marker_ok = 0;
    }
    if (!marker_ok) plen = buf_size - i; // unparsable remainder: one region
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = i + plen - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    i += plen;
    if (!marker_ok) break;
  }

  *region_count_ref = region_count;
  return regions;
}

unsigned int* extract_response_codes_bgp(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // State codes: 1=OPEN 2=UPDATE 3=NOTIFICATION(+major*10) 4=KEEPALIVE
  // 5=ROUTE-REFRESH, scanned packet by packet; initial state 0.
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  unsigned int i = 0;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (i + 19 <= buf_size) {
    unsigned int j, plen, code;
    int marker_ok = 1;
    for (j = i; j < i + 16; j++) if (buf[j] != 0xFF) { marker_ok = 0; break; }
    if (!marker_ok) break;
    plen = (buf[i + 16] << 8) | buf[i + 17];
    if (plen < 19 || i + plen > buf_size) break;
    switch (buf[i + 18]) {
      case 1: code = 1; break; // OPEN
      case 2: code = 2; break; // UPDATE
      case 3: code = (plen >= 21) ? (30 + buf[i + 19] * 10) : 30; break; // NOTIFICATION+major
      case 4: code = 4; break; // KEEPALIVE
      case 5: code = 5; break; // ROUTE-REFRESH
      default: code = 9; break;
    }
    state_count++;
    state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
    state_sequence[state_count - 1] = code;
    i += plen;
  }

  *state_count_ref = state_count;
  return state_sequence;
}


// SNMP over UDP: BER SEQUENCE framing. Length is short-form (<0x80) or
// long-form (0x8N + N big-endian bytes). An unparsable tail becomes one
// final region (mutation surface, server drops it).
static unsigned int snmp_ber_len(const unsigned char* b, unsigned int rem, unsigned int* hdrlen)
{
  unsigned int i, l;
  if (rem < 2) { *hdrlen = 0; return 0; }
  l = b[1];
  if (!(l & 0x80)) { *hdrlen = 2; return l; }
  unsigned int n = l & 0x7f;
  if (n == 0 || n > 4 || rem < 2 + n) { *hdrlen = 0; return 0; }
  l = 0;
  for (i = 0; i < n; i++) l = (l << 8) | b[2 + i];
  *hdrlen = 2 + n;
  return l;
}

static unsigned int snmp_content_len(const unsigned char* b, unsigned int rem, unsigned int* hdrlen)
{
  if (rem < 2 || b[0] != 0x30) { *hdrlen = 0; return 0; }
  return snmp_ber_len(b, rem, hdrlen);
}

// One BER TLV at pos inside [pos, end): its tag, content start and the
// position after it. Returns 0 when it does not fit.
static int snmp_tlv(const unsigned char* buf, unsigned int pos, unsigned int end,
                    unsigned int* tag, unsigned int* start, unsigned int* next)
{
  unsigned int hdrlen, len;
  if (pos >= end) return 0;
  len = snmp_ber_len(buf + pos, end - pos, &hdrlen);
  if (hdrlen == 0 || len > end - pos - hdrlen) return 0;
  *tag = buf[pos];
  *start = pos + hdrlen;
  *next = pos + hdrlen + len;
  return 1;
}

// The PDU tag of one message whose SEQUENCE content is [p, end), or 0:
// v1/v2c  version INTEGER, community OCTET STRING, PDU;
// v3      version INTEGER, msgGlobalData SEQUENCE, msgSecurityParameters
//         OCTET STRING, then the ScopedPDU SEQUENCE { contextEngineID,
//         contextName, PDU } or, encrypted, an OCTET STRING (code 0x100).
static unsigned int snmp_pdu_tag(const unsigned char* buf, unsigned int p, unsigned int end)
{
  unsigned int tag, start, next, version;
  if (!snmp_tlv(buf, p, end, &tag, &start, &next) || tag != 0x02 || start == next) return 0;
  version = buf[next - 1];
  p = next;
  if (version == 3) {
    if (!snmp_tlv(buf, p, end, &tag, &start, &next) || tag != 0x30) return 0;
    p = next;
    if (!snmp_tlv(buf, p, end, &tag, &start, &next) || tag != 0x04) return 0;
    p = next;
    if (!snmp_tlv(buf, p, end, &tag, &start, &next)) return 0;
    if (tag == 0x04) return 0x100;
    if (tag != 0x30) return 0;
    p = start;
    end = next;
    if (!snmp_tlv(buf, p, end, &tag, &start, &next) || tag != 0x04) return 0;
    p = next;
  }
  if (!snmp_tlv(buf, p, end, &tag, &start, &next) || tag != 0x04) return 0;
  p = next;
  // 0xA0 GetRequest ... 0xA2 Response ... 0xA7 SNMPv2-Trap, 0xA8 Report
  if (p < end && buf[p] >= 0xA0 && buf[p] <= 0xA8) return buf[p];
  return 0;
}

region_t* extract_requests_snmp(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  region_t *regions = NULL;
  unsigned int region_count = 0, i = 0;
  while (i < buf_size) {
    unsigned int hdrlen = 0, clen = snmp_content_len(buf + i, buf_size - i, &hdrlen);
    unsigned int mlen;
    if (hdrlen == 0 || clen > buf_size - i - hdrlen) mlen = buf_size - i; // unparsable: rest is one region
    else mlen = hdrlen + clen;
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = i + mlen - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    if (mlen == 0) break;
    i += mlen;
    if (hdrlen == 0) break;
  }
  *region_count_ref = region_count;
  return regions;
}

unsigned int* extract_response_codes_snmp(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // State code = the PDU tag byte (0xA2 Response, 0xA8 Report, ...; 0x100
  // for an encrypted v3 ScopedPDU), for SNMPv1, v2c and v3 alike. A
  // message whose inside does not parse adds no state; the walk goes on
  // with the next message, which the outer SEQUENCE length locates.
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0, i = 0;
  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;
  while (i < buf_size) {
    unsigned int hdrlen = 0, clen = snmp_content_len(buf + i, buf_size - i, &hdrlen);
    if (hdrlen == 0 || clen > buf_size - i - hdrlen) break;
    unsigned int p = i + hdrlen, end = p + clen;
    unsigned int code = snmp_pdu_tag(buf, p, end);
    if (code) {
      state_count++;
      state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
      state_sequence[state_count - 1] = code;
    }
    i = end;
  }
  *state_count_ref = state_count;
  return state_sequence;
}


region_t* extract_requests_pgsql(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  // PostgreSQL v3 frontend wire format: the FIRST message (startup) is
  // 4-byte BE length (self-inclusive) + params, no type byte; every later
  // message is 1 type byte + 4-byte BE length (covers itself, not the type
  // byte) + payload. Split accordingly; an unparsable tail becomes one
  // final region so mutants still reach the server.
  region_t *regions = NULL;
  unsigned int region_count = 0;
  unsigned int i = 0;
  int first = 1;

  while (i < buf_size) {
    unsigned int mlen;
    if (first) {
      if (buf_size - i < 4) { mlen = buf_size - i; }
      else {
        mlen = ((unsigned int)buf[i] << 24) | ((unsigned int)buf[i+1] << 16) |
               ((unsigned int)buf[i+2] << 8) | buf[i+3];
        if (mlen < 8 || mlen > buf_size - i) mlen = buf_size - i;
      }
      // An SSLRequest or GSSENCRequest (length 8, code 80877103/80877104)
      // is answered with one byte; the startup message that follows it is
      // untyped too.
      first = (mlen == 8 && buf[i+4] == 0x04 && buf[i+5] == 0xd2 && buf[i+6] == 0x16 &&
               (buf[i+7] == 0x2f || buf[i+7] == 0x30));
    } else {
      if (buf_size - i < 5) { mlen = buf_size - i; }
      else {
        unsigned int blen = ((unsigned int)buf[i+1] << 24) | ((unsigned int)buf[i+2] << 16) |
                            ((unsigned int)buf[i+3] << 8) | buf[i+4];
        if (blen < 4 || blen > buf_size - i - 1) mlen = buf_size - i;
        else mlen = 1 + blen;
      }
    }
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = i + mlen - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    i += mlen;
  }

  *region_count_ref = region_count;
  return regions;
}

unsigned int* extract_response_codes_pgsql(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // Backend messages: 1 type byte + 4-byte BE length (self-inclusive).
  // The state code IS the message type byte (R=auth, K=backend key,
  // Z=ready-for-query, T=row desc, D=data row, C=command complete,
  // E=error, S=parameter status, ...): injective, table-free, and mirrors
  // exactly what the client state machine observes. Initial state 0.
  // Before the first typed message, the one-byte answers to SSLRequest /
  // GSSENCRequest ('N' refused, 'S' / 'G' accepted) get 0x100 + byte.
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0;
  unsigned int i = 0;
  int typed = 0;

  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;

  while (i < buf_size) {
    unsigned int code, step;
    unsigned int blen = 0;
    if (buf_size - i >= 5)
      blen = ((unsigned int)buf[i+1] << 24) | ((unsigned int)buf[i+2] << 16) |
             ((unsigned int)buf[i+3] << 8) | buf[i+4];
    if (buf_size - i >= 5 && blen >= 4 && blen <= buf_size - i - 1) {
      code = buf[i];
      step = 1 + blen;
      typed = 1;
    } else if (!typed && (buf[i] == 'N' || buf[i] == 'S' || buf[i] == 'G')) {
      code = 0x100 + buf[i];
      step = 1;
    } else break;
    state_count++;
    state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
    state_sequence[state_count - 1] = code;
    i += step;
  }

  *state_count_ref = state_count;
  return state_sequence;
}


// RADIUS over UDP: code(1) id(1) length(2 BE, >=20, includes header)
// authenticator(16) attributes. Length-field split; unparsable tail = one
// final region.
region_t* extract_requests_radius(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  region_t *regions = NULL;
  unsigned int region_count = 0, i = 0;
  while (i < buf_size) {
    unsigned int plen;
    if (buf_size - i < 20) plen = buf_size - i;
    else {
      plen = ((unsigned int)buf[i+2] << 8) | buf[i+3];
      if (plen < 20 || i + plen > buf_size) plen = buf_size - i;
    }
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = i + plen - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    i += plen;
    if (plen < 20) break;
  }
  *region_count_ref = region_count;
  return regions;
}

unsigned int* extract_response_codes_radius(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // State code = the packet Code byte (2 Access-Accept, 3 Access-Reject,
  // 5 Accounting-Response, 11 Access-Challenge, ...): the AAA state
  // machine in one byte.
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0, i = 0;
  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;
  while (i + 20 <= buf_size) {
    unsigned int plen = ((unsigned int)buf[i+2] << 8) | buf[i+3];
    if (plen < 20 || i + plen > buf_size) break;
    state_count++;
    state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
    state_sequence[state_count - 1] = buf[i];
    i += plen;
  }
  *state_count_ref = state_count;
  return state_sequence;
}


// RDP over TCP: TPKT framing (03 00 + 2-byte BE length incl. the 4-byte
// header) wrapping X.224/MCS PDUs, and fast-path PDUs once the connection
// is up. Unparsable tail = one final region.

// Fast-path PDU (client input or server output): action bits 0-1 = 0,
// then the PDU length in 1 byte, or in 2 bytes (15 bits) when the first
// one has its top bit set. Returns the length, or 0 if not one.
static unsigned int rdp_fastpath_len(const unsigned char* b, unsigned int rem, unsigned int* hdrlen)
{
  unsigned int len;
  if (rem < 2 || (b[0] & 0x03) != 0) return 0;
  if (b[1] & 0x80) {
    if (rem < 3) return 0;
    len = ((unsigned int)(b[1] & 0x7f) << 8) | b[2];
    *hdrlen = 3;
  } else {
    len = b[1];
    *hdrlen = 2;
  }
  if (len < *hdrlen || len > rem) return 0;
  return len;
}

region_t* extract_requests_rdp(unsigned char* buf, unsigned int buf_size, unsigned int* region_count_ref)
{
  region_t *regions = NULL;
  unsigned int region_count = 0, i = 0;
  while (i < buf_size) {
    unsigned int plen = 0, hdrlen, rem = buf_size - i;
    if (rem >= 4 && buf[i] == 3 && buf[i+1] == 0) {
      plen = ((unsigned int)buf[i+2] << 8) | buf[i+3];
      if (plen < 4 || plen > rem) plen = 0;
    } else {
      plen = rdp_fastpath_len(buf + i, rem, &hdrlen);
    }
    int framed = (plen != 0);
    if (!framed) plen = rem;
    regions = (region_t *)ck_realloc(regions, (region_count + 1) * sizeof(region_t));
    regions[region_count].start_byte = i;
    regions[region_count].end_byte = i + plen - 1;
    regions[region_count].state_sequence = NULL;
    regions[region_count].state_count = 0;
    region_count++;
    i += plen;
    if (!framed) break;
  }
  *region_count_ref = region_count;
  return regions;
}

unsigned int* extract_response_codes_rdp(unsigned char* buf, unsigned int buf_size, unsigned int* state_count_ref)
{
  // State codes: X.224 TPDU code (0xD0 Connect-Confirm, 0xE0 Connect/Data
  // variants, 0xF0 DT-Data) refined by the first MCS payload byte for data
  // PDUs: code = x224, or 0x1000+payload for 0xF0 frames. Fast-path output
  // PDUs: 0x2000 + the update code of their first update (0x2FFF when
  // encrypted, 0x2FFE when empty).
  unsigned int *state_sequence = NULL;
  unsigned int state_count = 0, i = 0;
  state_count++;
  state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
  state_sequence[state_count - 1] = 0;
  while (i < buf_size) {
    unsigned int plen, hdrlen, code, rem = buf_size - i;
    if (rem >= 4 && buf[i] == 3 && buf[i+1] == 0) {
      plen = ((unsigned int)buf[i+2] << 8) | buf[i+3];
      if (plen < 4 || plen > rem) break;
      if (plen >= 6) {
        /* buf[i+4] is the X.224 LI byte; the TPDU code sits at buf[i+5] */
        unsigned char x = buf[i+5] & 0xF0;
        /* DT-Data: LI, 0xF0, EOT+credit, then user data at buf[i+7] */
        if (x == 0xF0 && plen >= 8) code = 0x1000 + buf[i+7];
        else code = x;
      } else code = 0xFF;
    } else if ((plen = rdp_fastpath_len(buf + i, rem, &hdrlen)) != 0) {
      if (buf[i] & 0x80) code = 0x2FFF;  // encrypted: signature, then ciphertext
      else if (plen > hdrlen) code = 0x2000 + (buf[i + hdrlen] & 0x0f);
      else code = 0x2FFE;
    } else break;
    state_count++;
    state_sequence = (unsigned int *)ck_realloc(state_sequence, state_count * sizeof(unsigned int));
    state_sequence[state_count - 1] = code;
    i += plen;
  }
  *state_count_ref = state_count;
  return state_sequence;
}
