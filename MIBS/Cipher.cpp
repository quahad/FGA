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

typedef unsigned long long UINT64;
typedef unsigned int UINT32;


//////////////////////////////////////////////////////////////////////////////
static int totalRounds = 0; // odd rounds
//UINT32 RoundKey[60];


//------------------------------------------------------------------------------------------------------------------------
static const int SBox [16] =
{
	4, 15, 3, 8, 13, 10, 12, 0, 11, 5, 7, 14, 2, 6, 1, 9  // Mcrypton First S_Box
};

//------------------------------------------------------------------------------------------------------------------------
#define M1(r1,r2,r3,r4,r5,r6) ( ((a<<(r1*4))^(a<<(r2*4))^(a<<(r3*4))^(a<<(r4*4))^(a<<(r5*4))^(a<<(r6*4))) )
#define M2(r1,r2,r3,r4,r5) ( ((a<<(r1*4))^(a<<(r2*4))^(a<<(r3*4))^(a<<(r4*4))^(a<<(r5*4))))
inline UINT32 Permutation ( UINT32 inputData )
{
	UINT32 res,a=inputData;

	res = M1(0,1,3,4,6,7)&0xF0000000;
	res |= (M1(1,2,3,4,5,6)>>4)&0x0F000000;
	res |= (M1(0,1,2,4,5,7)>>8)&0x00F00000;
	res |= (M2(1,2,3,6,7)>>12)&0x000F0000;
	res |= (M2(0,2,3,4,7)>>16)&0x0000F000;
	res |= (M2(0,1,3,4,5)>>20)&0x00000F00;
	res |= (M2(0,1,2,5,6)>>24)&0x000000F0;
	res |= (M1(0,2,3,5,6,7)>>28)&0x000000F;

	// Insert them into permutedData1
	return res;
}
//#define ROTR80H(L,R,n) {UINT64 tR=R>>n;UINT64 tt = L;tt<<=(64-n); tR^=tt; tt=0xFFFF;tt>>=(16-n);L=tt&R;R=tR;}
//#define ROTR80_19(L,R) {ROTR80H(L,R,16);ROTR80H(L,R,3)}

inline void ROTR80H(UINT64& L,UINT64& R,char n)
{
	UINT64 tR=R>>n;
	UINT64 tt = L;
	tt<<=(64-n);
	tR^=tt;
	tt=0xFFFF;
	tt>>=(16-n);
	L>>=n;
	L^=(tt&R)<<(16-n);
	R=tR;
}
inline void ROTR80_19(UINT64& L,UINT64& R)
{
	ROTR80H(L,R,16);
	ROTR80H(L,R,3);
}

//------------------------------------------------------------------------------------------------------------------------
inline void KeySchedule(UINT64 mKeyL,UINT64 mKeyR, UINT32 RoundKey[32])
{

	for ( int round = 1; round <= totalRounds; round++ )
	{

		// Apply left rotation ( rotate 61 most left bits to left)
		ROTR80_19(mKeyL,mKeyR);

		// Apply S_box to k79 k78 k77 k76
		UINT32 tmp;
		mKeyL = (SBox[(mKeyL&0xF000)>>12]<<12) | (SBox[(mKeyL&0xF00)>>8]<<8) | (mKeyL&0xFF);
		tmp = (round&0x1F);
		tmp <<= 14;
		mKeyR ^= tmp;
		//Fill the round keys
		RoundKey[round-1] = mKeyL<<16 | (mKeyR>>48);
	}

}
//------------------------------------------------------------------------------------------------------------------------
inline UINT32 F ( UINT32 leftData, UINT32 roundKey, int type = 0, uint32_t tap[2] = 0)
{
	UINT32 F_output=0, sboxOutput=0, permutedData, xoredData;
	UINT32 tmp, sTmp;

	/********************************************************/
	// Xored with Key schedule
    if(type==0)
        tap[0] = leftData;
	xoredData = leftData^roundKey;
    if(type==1)
        tap[0] = xoredData;
	/********************************************************/
	// Apply Substitution layer
	for ( int i = 0; i < 8; i++ )
	{
		// Read 4 bit 4 bit from left to right
		tmp = xoredData&0xF;
		tmp = SBox[tmp];
		tmp <<= 28;
		sboxOutput^=tmp;
		xoredData>>=4;
		if(i!=7)
		sboxOutput>>=4;
	}
	/********************************************************/
    tap[1]=sboxOutput;
	// Apply Permutation layer
	permutedData = Permutation ( sboxOutput );
	/********************************************************/
	F_output = permutedData;
	return F_output;
}

//------------------------------------------------------------------------------------------------------------------------
inline UINT64 encipher ( UINT64 plainText, UINT64 mKeyL,UINT64 mKeyR, int round )
{
	UINT32 RoundKey[32];
	KeySchedule ( mKeyL,mKeyR,RoundKey );

	UINT64 cipherText;
	UINT32 leftData, rightData, xorLeftRight, F_output /*,leftData_Permuted*/ ;

	// Divide plainText in to two part left and right

	leftData = plainText>>32;
	rightData = plainText;

	for ( int rnd = 0; rnd < round; rnd++ )
	{

		F_output = F (leftData, RoundKey [ rnd ] );

		xorLeftRight = F_output ^ rightData;

		// exchange right and left data
		rightData = leftData;
		leftData = xorLeftRight;

	}

	// left and right data don't exchange last round
	cipherText = rightData;
	cipherText<<=32;
	cipherText|=leftData;

	return cipherText;
}

const int KeySchedSize = 80+8*32;
void* SetKey(int nr, bitset<KeySchedSize>& key)
{
	totalRounds=nr;
	__uint32_t* rk = (__uint32_t*)malloc(nr*sizeof(__uint32_t));

	UINT64 mKeyL=0,mKeyR=0;

	for(int i=64;i<80;i++)
		if(key[i])
			mKeyL ^= ((UINT64)0x1)<<(i-64);
	for(int i=0;i<64;i++)
		if(key[i])
			mKeyR ^= ((UINT64)0x1)<<i;

	KeySchedule(mKeyL,mKeyR,rk);
    for(int i=0;i<nr;i++)
	{
		for(int j=0;j<8;j++)
			key[80+i*8+j]=(rk[i]>>(24+j))&0x1;
	}
	return rk;
}

__uint64_t encryptTap(int type,__uint64_t plainText,const void* ctx,__uint32_t tap[][2])
{
	const __uint32_t* RoundKey = (const __uint32_t*)ctx;
	UINT64 cipherText;
		UINT32 leftData, rightData, xorLeftRight, F_output /*,leftData_Permuted*/ ;
		
		// Divide plainText in to two part left and right

		leftData = plainText>>32;
		rightData = plainText;

		for ( int rnd = 0; rnd < totalRounds; rnd++ )
		{

			F_output = F (leftData, RoundKey [ rnd ] ,type , tap[rnd] );

			xorLeftRight = F_output ^ rightData;

			// exchange right and left data
			rightData = leftData;
			leftData = xorLeftRight;

		}
	


		// left and right data don't exchange last round
		cipherText = rightData;
		cipherText<<=32;
		cipherText|=leftData;

		return cipherText;
}

__uint64_t decryptTap(int type,__uint64_t cipherText,const void* ctx,__uint32_t tap[][2])
{
    const __uint32_t* RoundKey = (const __uint32_t*)ctx;
	UINT64 plainText;
	UINT32 leftData, rightData, xorLeftRight, F_output /*,leftData_Permuted*/ ;
    rightData = cipherText>>32;
    leftData = cipherText&0xFFFFFFFF;
    
    for ( int rnd = totalRounds-1; rnd >=0; rnd--)
	{
        xorLeftRight = leftData;
        leftData = rightData;
        F_output = F (leftData, RoundKey [ rnd ] ,type , tap[rnd]);
		rightData = F_output ^ xorLeftRight;

	}
	
    plainText = leftData;
    plainText<<=32;
    plainText ^= rightData;

    return plainText;
}
