//============================================================================
// Name        : LBlock.cpp
// Author      : hossein
// Version     :
// Copyright   : Your copyright notice
// Description : Hello World in C++, Ansi-style
//============================================================================


#include <stdlib.h>
#include <bitset>

using namespace std;
typedef unsigned long long UINT64;
typedef unsigned int UINT32;




const unsigned short S[10][16]={{14,9,15,0,13,4,10,11,1,2,8,3,7,6,12,5},{4,11,14,9,15,13,0,10,7,12,5,6,2,8,1,3},{1,14,7,12,15,13,0,6,11,5,9,3,2,4,8,10},
				{7,6,8,11,0,15,3,14,9,10,12,13,5,2,4,1},{14,5,15,0,7,2,12,13,1,8,4,9,11,10,6,3},{2,13,11,12,15,14,0,9,7,10,6,3,1,8,4,5},
				{11,9,4,14,0,15,10,13,6,12,5,7,3,8,1,2},{13,10,15,0,14,4,9,11,2,1,8,3,7,5,12,6},{8,7,14,5,15,13,0,6,11,12,9,10,2,4,1,3},
				{11,5,15,0,7,2,9,13,4,8,1,12,14,10,3,6}};


const unsigned short P[8]={1,3,0,2,5,7,4,6};
const int max_rnd=32;
static unsigned int rounds=32;
/*
extern "C"
{
	void roundkey(int rnds,const __uint32_t k[5],__uint32_t rk[]);
	__uint64_t encryptTap(__uint64_t ptext,const __uint32_t rk[],__uint32_t tap[]);
	void find_valid_diff(int rnds,UINT64 msk_in,UINT64 msk_out,UINT32 k1[5],UINT64 xx[2]);
	void find_min_diff(int rnds,UINT64 msk_in,UINT32 k1[5],UINT64 xx[2]);
}*/

void roundkey(int rnds,const __uint32_t kk[5],__uint32_t rk[]){

	unsigned int i,t1,t2,t3,t4,t0,c1,c2;
	__uint32_t k[5];
	k[0]=kk[0];
	k[1]=kk[1];
	k[2]=kk[2];
	k[3]=kk[3];
	k[4]=kk[4];

	rounds=rnds;
	rk[0]=(k[0]<<16)^ k[1];
	for(i=1;i<rounds;i++){
		// 32 left shift (then 3 right shift)
		t1=k[0]; t2=k[1];
		k[0]=k[2];  k[1]=k[3]; k[2]=k[4]; k[3]=t1; k[4]=t2;
		//3 right shift
		t0=(k[0]&0x7); 		t1=(k[1]&0x7);		t2=(k[2]&0x7);
		t3=(k[3]&0x7); 		t4=(k[4]&0x7);
		k[4]=(k[4]>>3)^(t3<<13);
		k[3]=(k[3]>>3)^(t2<<13);
		k[2]=(k[2]>>3)^(t1<<13);
		k[1]=(k[1]>>3)^(t0<<13);
		k[0]=(k[0]>>3)^(t4<<13);
		//s-box
		t1=(k[0]>>12)&0xF;
		t2=(k[0]>>8)&0xF;
		t1=S[9][t1];
		t2=S[8][t2];
		k[0]=(t1<<12)^(t2<<8)^(k[0]&0x00FF);
		//counter
		c1=i&0x3; c2=i>>2;
		k[2]^=c1<<14; k[1]^=c2;
		//get roundkey
		rk[i]=(k[0]<<16)^ k[1];
	}
}

unsigned int S_Layer(unsigned int x){
	unsigned int temp=0x0;
	int i;
	for(i=0;i<7;i++){
		temp^=S[7-i][(x>>(28-4*i))&0xF];
		temp<<=4;
	}
	temp^=S[7-i][x&0xF];
	return temp;
}

unsigned int P_Layer(unsigned int x){
	unsigned short temp[8],i;
	unsigned int t=0x0;

	for(i=0;i<8;i++)
		temp[i]=(x>>(28-(4*i)))&0xF;

	for(i=0;i<7;i++){
		t^=temp[P[i]];
		t<<=4;
	}
	t^=temp[P[i]];

	return t;
}

unsigned int F(unsigned int x, unsigned int k,int type = 0, uint32_t tap[2] = 0){
    if(type==0)
        tap[0] = x;
	x^=k;
    if(type==1)
        tap[0] = x;
	x=S_Layer(x);
    tap[1] = x;
	x=P_Layer(x);
	return x;
}
void swap(unsigned int *left, unsigned int *right){
	unsigned int temp;
	temp=(*left);
	(*left)=(*right);
	(*right)=temp;
}

const int KeySchedSize = 80+8*31;
void* SetKey(int nr, bitset<KeySchedSize>& key)
{
	__uint32_t kk[5]={0,0,0,0,0};
	__uint32_t* rk = (__uint32_t*)malloc(nr*sizeof(__uint32_t));

	for(int i=0;i<80;i++)
		if(key[i])
			kk[4-(i/16)] ^= 0x1<<(i%16);
	roundkey(nr,kk,rk);
	for(int i=0;i<nr-1;i++)
	{
		for(int j=0;j<8;j++)
			key[80+i*8+j]=(rk[i+1]>>(24+j))&0x1;
	}
	return rk;
}

void* SetKey2(int nr, const bitset<80>& key)
{
	__uint32_t kk[5]={0,0,0,0,0};
	__uint32_t* rk = (__uint32_t*)malloc(nr*sizeof(__uint32_t));

	for(int i=0;i<80;i++)
		if(key[i])
			kk[4-(i/16)] ^= 0x1<<(i%16);
	roundkey(nr,kk,rk);
	return rk;
}



__uint64_t encryptTap(int type,__uint64_t ptext,const void* ctx,__uint32_t tap[][2])
{
	UINT64 ctext;
	UINT32 left, right;
    const uint32_t* rk1=(uint32_t*)ctx;
	left=ptext>>32;
	right=ptext&0xFFFFFFFF;
	for(int i=0;i<rounds;i++){
		right=(right<<8)^(right>>24);
		right^=F(left,rk1[i],type,tap[i]);
		swap(&left,&right);
	}

	ctext=right;
	ctext<<=32;
	ctext^=left;
	return ctext;
}

__uint64_t decryptTap(int type,__uint64_t ctext,const void* ctx,__uint32_t tap[][2])
{
    UINT64 ptext;
	UINT32 left, right;
	const uint32_t* rk1=(uint32_t*)ctx;
	right=ctext>>32;
	left=ctext&0xFFFFFFFF;
	for(int i=rounds-1;i>=0;i--){
		swap(&left,&right);
		right^=F(left,rk1[i],type,tap[i]);
		right=(right>>8)^(right<<24);
	}

	ptext=left;
	ptext<<=32;
	ptext^=right;
	return ptext;

}
