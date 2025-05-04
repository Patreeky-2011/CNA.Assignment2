#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "sr.h"

/* ******************************************************************
   Go Back N protocol.  Adapted from J.F.Kurose
   ALTERNATING BIT AND GO-BACK-N NETWORK EMULATOR: VERSION 1.2  

   Network properties:
   - one way network delay averages five time units (longer if there
   are other messages in the channel for GBN), but can be larger
   - packets can be corrupted (either the header or the data portion)
   or lost, according to user-defined probabilities
   - packets will be delivered in the order in which they were sent
   (although some can be lost).

   Modifications: 
   - removed bidirectional GBN code and other code not used by prac. 
   - fixed C style to adhere to current programming style
   - added GBN implementation
**********************************************************************/

#define RTT  16.0       /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6    /* the maximum number of buffered unacked packet */
#define SEQSPACE 13      /* the min sequence space for GBN must be at least windowsize + 1 */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver  
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your 
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
  int checksum = 0;
  int i;

  checksum = packet.seqnum;
  checksum += packet.acknum;
  for ( i=0; i<20; i++ ) 
    checksum += (int)(packet.payload[i]);

  return checksum;
}

bool IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (false);
  else
    return (true);
}

/* This function covers wrap around logic so old ACKs don't get misinterpreted*/
bool isInWindow(int base, int seqnum) {
    if (base <= (base + WINDOWSIZE - 1) % SEQSPACE) {
        /* no wraparound*/ 
        return seqnum >= base && seqnum < base + WINDOWSIZE;
    } else {
        /* wraparound */
        return seqnum >= base || seqnum < (base + WINDOWSIZE) % SEQSPACE;
    }
}


/********* Sender (A) variables and functions ************/

static struct pkt buffer[SEQSPACE];  /* array for storing packets waiting for ACK (seqspace for sr)*/
static bool acked[SEQSPACE];         /* tracks if packets have been acked */
static int current_tick = 0;         /*  This will be the global clock */
static int due_tick[SEQSPACE];       /*This tracks 'expiry' times*/
/*timeout period (RTT * 1.5 = 24)*/
static int timeout_ticks = 24;         /*ticks before timeout (24/1.0 = 24)*/
/*static float tick_interval = 1;      this is how often to call timer_interrupt*/
int timer_running = 0;

static struct pkt B_buffer[SEQSPACE]; 
static int B_received[SEQSPACE]; 

static int windowfirst, windowlast;    /* array indexes of the first/last packet awaiting ACK */
static int windowcount;                /* the number of packets currently awaiting an ACK */
static int A_nextseqnum;               /* the next sequence number to be used by the sender */


/*VARIABLES FOR BIDIRECTIONAL TRAVEL*/
static bool B_acked[SEQSPACE];
static int B_windowfirst, B_windowlast, B_windowcount;
static int B_nextseqnum = 0;
static int B_window_full = 0;

/* called from layer 5 (application layer), passed the message to be sent to other side */
  void A_output(struct msg message)
  {
    struct pkt sendpkt;
    int i;

    /* if not blocked waiting on ACK */
    if ( windowcount < WINDOWSIZE) {
      if (TRACE > 1)
        printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

      /* create packet */
      sendpkt.seqnum = A_nextseqnum;
      sendpkt.acknum = NOTINUSE;
      for ( i=0; i<20 ; i++ ) 
        sendpkt.payload[i] = message.data[i];
      sendpkt.checksum = ComputeChecksum(sendpkt); 

      /* put packet in window buffer */
      /* windowlast will always be 0 for alternating bit; but not for GoBackN */
      /*windowlast = (windowlast + 1) % WINDOWSIZE; 
      buffer[windowlast] = sendpkt;*/

      buffer[sendpkt.seqnum] = sendpkt;
      acked[sendpkt.seqnum] = 0; /*ACK has not been received so 0*/
      due_tick[sendpkt.seqnum] = current_tick + timeout_ticks;

      /* send out packet */
      if (TRACE > 0)
        printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
      tolayer3 (A, sendpkt);

      windowcount++;

      /* Only one timer so store send times, and then only start timer if not already running. */
      /*if (windowcount==1) {
        starttimer(A, timeout_ticks);
      */ 
      if (!timer_running) {
        starttimer(A, timeout_ticks);  
        timer_running = 1;
      }

      /* get next sequence number, wrap back to 0 */
      A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;  
    }
    /* if blocked,  window is full */
    else {
      if (TRACE > 0)
        printf("----A: New message arrives, send window is full\n");
      window_full++;
    }
  }


/* called from layer 3, when a packet arrives for layer 4 
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{

  /* if received ACK is not corrupted */ 
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: uncorrupted ACK %d is received\n",packet.acknum);
    total_ACKs_received++;

    /* check if new ACK or duplicate */
    if (!acked[packet.acknum]) {
      acked[packet.acknum] = 1;

      /* No need for wrap around logic because seqnum is used and no cum acks. */
      /* packet is a new ACK */
      if (TRACE > 0)
        printf("----A: ACK %d is not a duplicate\n",packet.acknum);
      new_ACKs++;

      /*When earliest unACK'ed packets have been acked, slide the window*/
      while (acked[windowfirst]) {
        acked[windowfirst] = 0;  
        due_tick[windowfirst] = 0;
        buffer[windowfirst].seqnum = -1;  
        windowfirst = (windowfirst + 1) % SEQSPACE;
        windowcount--;
      }

	    /* start timer again if there are still more unacked packets in window */
      if (windowcount > 0) {
        stoptimer(A);
        starttimer(A, timeout_ticks);  
        timer_running = 1;
      } else {
        stoptimer(A);
        timer_running = 0;
      }
    } else
      if (TRACE > 0)
      printf ("----A: duplicate ACK received, do nothing!\n");
  }
  else 
    if (TRACE > 0)
      printf ("----A: corrupted ACK is received, do nothing!\n");
}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
  int i;
  int seqnum;
  int has_unacked = 0;
  current_tick++;

  if (TRACE > 0)
    printf("----A: time out,resend packets!\n");

    for (i = 0; i < windowcount; i++) {
      seqnum = (windowfirst + i) % SEQSPACE;
  
      if (!acked[seqnum]) {
        if (TRACE > 0)
          printf("---A: resending packet %d\n", buffer[seqnum].seqnum);
  
        tolayer3(A, buffer[seqnum]);
        has_unacked = 1;
      }
    }
  
    if (has_unacked) {
      stoptimer(A);  // Ensure clean restart
      starttimer(A, timeout_ticks);
      timer_running = 1;
    } else {
      stoptimer(A);
      timer_running = 0;
    }
  }

/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
  /* initialise A's window, buffer and sequence number */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  windowfirst = 0;
  windowlast = -1;   /* windowlast is where the last packet sent is stored.  
		     new packets are placed in winlast + 1 
		     so initially this is set to -1
		   */
  windowcount = 0;
}



/********* Receiver (B)  variables and procedures ************/

/* These variables are for B section*/
             

static int expectedseqnum; /* the sequence number expected next by the receiver */
static int B_nextseqnum;   /* the sequence number for the next packets sent by B */


/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
  struct pkt sendpkt;
  int i;
  int seq = packet.seqnum;

  /* if not corrupted and received packet is in order */
  if  ( (!IsCorrupted(packet))) {
    int upper;
    int in_window;
    if (TRACE > 0)
      printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
    packets_received++;

    upper = (expectedseqnum + WINDOWSIZE) % SEQSPACE;
    in_window = (expectedseqnum <= upper)
                    ? (seq >= expectedseqnum && seq < upper)
                    : (seq >= expectedseqnum || seq < upper);

    
    if (in_window) {
      if (!B_received[seq]) {
        B_received[seq] = 1;
        B_buffer[seq] = packet;

        if (TRACE > 0)
          printf("----B: packet %d received and buffered\n", seq);
      } else {
        if (TRACE > 0)
          printf("----B: duplicate packet %d received, already buffered\n", seq);
      }

      sendpkt.seqnum = 0;
      sendpkt.acknum = seq;
      for (i = 0; i < 20; i++)
        sendpkt.payload[i] = '0';
      sendpkt.checksum = ComputeChecksum(sendpkt);
      tolayer3(B, sendpkt);


      while (B_received[expectedseqnum]) {
        tolayer5(B, B_buffer[expectedseqnum].payload);
        packets_received++;

        B_received[expectedseqnum] = 0;   
        expectedseqnum = (expectedseqnum + 1) % SEQSPACE;
      }
    } else {

      sendpkt.seqnum = 0;
      sendpkt.acknum = (expectedseqnum == 0) ? SEQSPACE - 1 : expectedseqnum - 1;
      for (i = 0; i < 20; i++)
        sendpkt.payload[i] = '0';
      sendpkt.checksum = ComputeChecksum(sendpkt);
      tolayer3(B, sendpkt);
    }
  }
  else {
    /* packet is corrupted or out of order, resend last ACK */
    int last_ack;
    if (TRACE > 0) 
      printf("----B: packet corrupted or not expected sequence number, resend ACK!\n");

    last_ack = (expectedseqnum == 0) ? SEQSPACE - 1 : expectedseqnum - 1;

    sendpkt.seqnum = 0;
    sendpkt.acknum = last_ack;
    for (i = 0; i < 20; i++)
        sendpkt.payload[i] = '0';
    sendpkt.checksum = ComputeChecksum(sendpkt);
    tolayer3(B, sendpkt);
  }
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
  int i;
  expectedseqnum = 0;
  B_nextseqnum = 1;
  for (i = 0; i < SEQSPACE; i++) {
    B_received[i] = 0;
  }
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)  
{
  struct pkt sendpkt;
  int i;

  /* if window is not full */
  if (B_windowcount < WINDOWSIZE) {
    if (TRACE > 1)
      printf("----B: New message arrives, send window is not full, send new message to layer3!\n");

    sendpkt.seqnum = B_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for (i = 0; i < 20; i++)
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt);

    B_windowlast = (B_windowlast + 1) % WINDOWSIZE;
    B_buffer[B_windowlast] = sendpkt;
    B_windowcount++;

    if (TRACE > 0)
      printf("Sending packet %d from B to layer 3\n", sendpkt.seqnum);
    tolayer3(B, sendpkt);

    B_acked[B_windowlast] = 0;

    if (B_windowcount == 1) {
      starttimer(B, timeout_ticks);
    }

    B_nextseqnum = (B_nextseqnum + 1) % SEQSPACE;
  } else {
    if (TRACE > 0)
      printf("----B: New message arrives, send window is full\n");
    B_window_full++;
  }
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
  int i;

  if (TRACE > 0)
    printf("----B: Timeout, resending packets!\n");

  for (i = 0; i < B_windowcount; i++) {
    if (TRACE > 0)
      printf("---B: resending packet %d\n", B_buffer[(B_windowfirst + i) % WINDOWSIZE].seqnum);

    tolayer3(B, B_buffer[(B_windowfirst + i) % WINDOWSIZE]);
    if (i == 0) starttimer(B, timeout_ticks);
  }
}

