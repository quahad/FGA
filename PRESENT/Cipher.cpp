//============================================================================
// Name        : MIBS.cpp
// Author      : hossein
// Version     :
// Copyright   : Your copyright notice
// Description : Hello World in C++, Ansi-style
//============================================================================

#include <iostream>
#include <bitset>
using namespace std;

typedef __uint64_t UINT64;
typedef __uint32_t UINT32;

#define high1_64(h1in) 			( (__uint64_t)h1in >> 63 )	//msb as lsb
#define high4_64(h4in) 			( (__uint64_t)h4in >> 60 )	//4 msb as lsb
#define rotate1l_64(r1lin)	 ( high1_64(r1lin) | ( r1lin << 1 ) )	//input rotated left (1x)
#define rotate4l_64(r4lin)	 ( high4_64(r4lin) | ( r4lin << 4 ) )	//input rotated left (4x)


//////////////////////////////////////////////////////////////////////////////
static int totalRounds = 0; // odd rounds
//UINT32 RoundKey[60];


//------------------------------------------------------------------------------------------------------------------------
const __uint16_t invsBox4[] = {0x5,0xe,0xf,0x8,0xC,0x1,0x2,0xD,0xB,0x4,0x6,0x3,0x0,0x7,0x9,0xA};
const __uint64_t sBox4[] = {0xc,0x5,0x6,0xb,0x9,0x0,0xa,0xd,0x3,0xe,0xf,0x8,0x4,0x7,0x1,0x2};



//------------------------------------------------------------------------------------------------------------------------
inline void KeySchedule(UINT64 mKeyL,UINT64 mKeyR, UINT64 RoundKey[32])
{
    __uint64_t keyhigh=mKeyL;
	__uint64_t keylow=mKeyR;

	for ( int round = 0; round < totalRounds+1; round++ )
	{

			RoundKey[round] = keyhigh;							//61-bit left shift
			__uint64_t temp = keyhigh;
			keyhigh <<= 61;
			keyhigh |= (keylow<<45);
			keyhigh |= (temp>>19);
			keylow = (temp>>3)&0xFFFF;

			temp = keyhigh>>60;									//S-Box application
			keyhigh &=	0x0FFFFFFFFFFFFFFF;
			temp = sBox4[temp];
			keyhigh |= temp<<60;

			keylow ^= ( ( (round+1) & 0x01 ) << 15 );			//round counter addition
			keyhigh ^= ( (round+1) >> 1 );
	}

}
//------------------------------------------------------------------------------------------------------------------------
const int KeySchedSize = 80+4*32;
void* SetKey(int nr, bitset<KeySchedSize>& key)
{
	totalRounds=nr;
	__uint64_t* rk = (__uint64_t*)malloc((nr+1)*sizeof(__uint64_t));

	UINT64 mKeyL=0,mKeyR=0;

	for(int i=16;i<80;i++)
		if(key[i])
			mKeyL ^= ((UINT64)0x1)<<(i-16);
	for(int i=0;i<16;i++)
		if(key[i])
			mKeyR ^= ((UINT64)0x1)<<i;

	KeySchedule(mKeyL,mKeyR,rk);
    for(int i=1;i<nr+1;i++)
	{
		for(int j=0;j<4;j++)
			key[80+(i-1)*4+j]=(rk[i]>>(60+j))&0x1;
	}
	return rk;
}

__uint64_t encryptTap(int type,__uint64_t plainText,const void* ctx,__uint64_t tap[][2])
{
	const __uint64_t* RoundKey = (const __uint64_t*)ctx;
	UINT64 temp,sBoxValue,state=plainText;
    int i,sBoxNr;
    
    

		for(i=0;i<totalRounds;i++)
		{
			state ^= RoundKey[i];
            if(type==1)
                tap[i][0]=state;
			for(sBoxNr=0;sBoxNr<16;sBoxNr++)
			{
				sBoxValue = state & 0xF;						//get lowest nibble
				state &=	0xFFFFFFFFFFFFFFF0UL;					//kill lowest nibble
				state |=	sBox4[sBoxValue];					//put new value to lowest nibble (sBox)
				state = rotate4l_64(state);						//next(rotate by one nibble)
			}
//	****************** End sBoxLayer ***********************
            if(type==1)
                tap[i][1]=state;
            else    
                tap[i][0]=state;
//	****************** pLayer ******************************
			temp = 0;
			for(int k=0;k<64;k++)
			{
				int position = (16*k) % 63;						//Arithmentic calculation of the p-Layer
				if(k == 63)										//Exception for bit 63			
					position = 63;
				temp |= ((state>>k) & 0x1) << position;			//result writing
			}
			state=temp;
//	****************** End pLayer **************************
        
		}
//	****************** addRoundkey (Round 31) **************
		state ^= RoundKey[totalRounds];
//	****************** End addRoundkey (Round 31) **********

	
		return state;
}

__uint64_t decryptTap(int type,__uint64_t cipherText,const void* ctx,__uint64_t tap[][2])
{
    const __uint64_t* RoundKey = (const __uint64_t*)ctx;
	UINT64 temp,sBoxValue,state=cipherText;
    int i,sBoxNr,keyindex;
    
      
    //	****************** Decryption **************************
		keyindex = totalRounds;
		for(i=0;i<totalRounds;i++)
		{
//	****************** addRoundkey *************************
			state ^= RoundKey[keyindex];
			keyindex--;
//	****************** End addRoundkey *********************
//	****************** pLayer ******************************
			temp = 0;
			for(int k=0;k<64;k++)
			{
				int position = (4*k) % 63;						//Arithmentic calculation of the p-Layer
				if(k == 63)										//Exception for bit 63
					position = 63;
				temp |= ((state>>k) & 0x1) << position;			//result writing
			}
			state=temp;
//	****************** End pLayer **************************
            if(type==1)
                tap[totalRounds-i-1][1]=state;
            else
                tap[totalRounds-i-1][0]=state;
//	****************** sBoxLayer ***************************
			for(sBoxNr=0;sBoxNr<16;sBoxNr++)
			{
				sBoxValue = state & 0xF;						//get lowest nibble
				state &=	0xFFFFFFFFFFFFFFF0;					//kill lowest nibble
				state |=	invsBox4[sBoxValue];				//put new value to lowest nibble (sbox)
				state = rotate4l_64(state);						//next(rotate by one nibble)
			}
//	****************** End sBoxLayer ***********************
            if(type==1)
                tap[totalRounds-i-1][0]=state;

		}
//	****************** addRoundkey (Round 31) **************
		state ^= RoundKey[0];
//	****************** End addRoundkey (Round 31) **********
	
//	****************** End Decryption **********************

	
   return state;
}
