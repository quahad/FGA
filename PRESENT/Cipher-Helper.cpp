//============================================================================
// Name        : Present-Num-Helper.cpp
// Author      : 
// Version     :
// Copyright   : Your copyright notice
// Description : Hello World in C++, Ansi-style
//============================================================================

#include <iostream>
#include <random>
#include <polybori/polybori.h>
#include <polybori/groebner/GroebnerStrategy.h>
#include <polybori/groebner/nf.h>
#include <polybori/groebner/red_tail.h>
#include <polybori/groebner/RedTailNth.h>
#include <polybori/groebner/interpolate.h>
#include <polybori/groebner/LiteralFactorization.h>
#include <m4ri/m4ri.h>
#include <omp.h>
#include <algorithm>

using namespace std;
using namespace polybori;

#define INT_TYPE 	    __uint64_t
#define INT_BIT_SIZE 	    64
#define CIPHER_STRING       "PRESENT80"
#define STRATEGY    	    CHOSEN_PLAINTEXT
#define GUESS_BITS          0
#define KEY_GUESS_STRATEGY  RIGHT_KEY_GUESS
#define CONSIDER_KEY_VARS   true
#define CUBE_LIKE_SAMPLES   false
#define PRINT_KEY   	    false
#define CHECK_ENCRYPT_EQS   false
#define REPORT_GROBNER      false
#define REPORT_PRONE        false
#define FORWARD_ONLY        false
#define POLYNOMIAL_ANALYSIS false
#define NUM_SBOX_EQS        8


const int NumTest = 10;
const int Nr = 8;
const int Nm = 512;
const int KeySize = 80;
const int KeySchedSize = 80+4*32;
const int NumKeys = 80+4*Nr;
const int NumVars = NumKeys + Nm*Nr*64;

vector<int> patt = { 0,1,2,3,4,5,6,7,8,9,10,11};
//vector<int> patt = { 4,5,6,7,8,9,10,11};
//vector<int> patt = { 28,29,30,31,44,45,46,47,48};
BoolePolyRing ring(NumVars,CTypes::dp_asc);
vector<BooleVariable> var_Keys(NumKeys,ring);
vector< vector< vector<BooleVariable> > > var_L(Nm,vector< vector<BooleVariable> >(Nr,vector<BooleVariable>(64,ring)));

vector<string> str_Keys(NumKeys);
vector< vector< array<string,64> > > str_L(Nm);


uint64_t ToStateXY(uint64_t X)
{
    return X;
}

uint64_t ToStateI(uint64_t X)
{
    return X;
}

#define LIN_ANALYSIS_START_ROUND 0
#define LIN_ANALYSIS_LAST_ROUND  (Nr-1)

                       
#include "../shared.h"



vector<BoolePolynomial> PrsBoxAddFWBW(const vector<BoolePolynomial>& X, const vector<BoolePolynomial>& Y)
{
	vector<BoolePolynomial> v(8,ring);
		v[0] = Y[0] + X[0] + X[1]*X[2] + X[2] + X[3];
		v[1] = Y[1] + X[0]*X[1]*X[2] + X[0]*X[1]*X[3] + X[0]*X[2]*X[3] + X[1]*X[3] + X[1] + X[2]*X[3] + X[3];
		v[2] = Y[2] + X[0]*X[1]*X[3] + X[0]*X[1] + X[0]*X[2]*X[3] + X[0]*X[3] + X[1]*X[3] + X[2] + X[3] + 1;
		v[3] = Y[3] + X[0]*X[1]*X[2] + X[0]*X[1]*X[3] + X[0]*X[2]*X[3] + X[0] + X[1]*X[2] + X[1] + X[3] + 1;
		v[4] = X[0] + Y[0] + Y[1]*Y[3] + Y[2] + 1;
		v[5] = X[1] + Y[0]*Y[1]*Y[2] + Y[0]*Y[1]*Y[3] + Y[0]*Y[2]*Y[3] + Y[0]*Y[2] + Y[0] + Y[1]*Y[3] + Y[1] + Y[2]*Y[3] + Y[3];
		v[6] = X[2] + Y[0]*Y[1]*Y[2] + Y[0]*Y[1]*Y[3] + Y[0]*Y[1] + Y[0]*Y[2]*Y[3] + Y[0]*Y[2] + Y[0]*Y[3] + Y[1]*Y[2] + Y[1]*Y[3] + Y[3] + 1;
		v[7] = X[3] + Y[0]*Y[1]*Y[2] + Y[0]*Y[1] + Y[0]*Y[2]*Y[3] + Y[0] + Y[1] + Y[2] + Y[3];

	return v;

}

vector<BoolePolynomial> SboxAdd(const vector<BoolePolynomial>& X, const vector<BoolePolynomial>& Y, int idx)
{
	return PrsBoxAddFWBW(X,Y);

}

const int mapPer[] = {0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 1, 5, 9,
13, 17, 21, 25, 29, 33, 37, 41, 45, 49, 53, 57, 61, 2, 6, 10, 14, 18,
22, 26, 30, 34, 38, 42, 46, 50, 54, 58, 62, 3, 7, 11, 15, 19, 23, 27,
31, 35, 39, 43, 47, 51, 55, 59, 63};
vector<BoolePolynomial> PBox(vector<BoolePolynomial> X)
{
    vector<BoolePolynomial> t(64,ring);
    for(int i=0;i<64;i++)
        t[i] = X[mapPer[i]];
    return t;
}


void PrsKeyRoundEqsMQ(vector<BoolePolynomial>& keqs,int rnd,vector<BoolePolynomial>& Stt)
{
	vector<BoolePolynomial> T(80,ring);
	for(int i=0;i<80;i++)
		T[(i-19+80)%80] = Stt[i];
	auto it_T=T.begin();
	auto it_k =var_Keys.begin();

	vector<BoolePolynomial> ee = SboxAdd(vector<BoolePolynomial>(it_T+76,it_T+80),vector<BoolePolynomial>(it_k+80+rnd*4,it_k+80+rnd*4+4));
	move(ee.begin(),ee.end(),inserter(keqs,keqs.end()));
	for(int i=0;i<4;i++)
		T[76+i] = var_Keys[80+rnd*4+i];
	for(int i=0;i<5;i++)
		T[15+i] += (((rnd+1)>>i)&0x1);
	Stt=T;
}


void AIOEncryptEqs(vector<BoolePolynomial>& eqs,
                       const vector<BoolePolynomial>& forward_eqs,
                       const bitset<IGNORE_BITSET_SIZE>& ignore_set,
                       const vector<BoolePolynomial>& K,
                       const vector< vector<BoolePolynomial> >& X,
                       const vector< vector<BoolePolynomial> >& Y)
{
	vector<BoolePolynomial> Stt=K;
    vector<vector<BoolePolynomial> > TT(Nm,vector<BoolePolynomial>(64,ring));
	vector< vector< vector<BoolePolynomial> > > T(Nm,vector< vector<BoolePolynomial> >(Nr,vector<BoolePolynomial>(64,ring)));
	for(int i=0;i<Nm;i++)
	{
		for(int j=0;j<64;j++)
		{
			TT[i][j] = X[i][j];
        }
		for(int j=0;j<Nr;j++)
		{
			for(int k=0;k<64;k++)
			{
				T[i][j][k] = var_L[i][j][k];
			}
		}
	}

    for( auto it=forward_eqs.begin();it!=forward_eqs.end();it++)
    {
        if(it->deg() == 1 && it->length() <= VARIABLE_ELIMLEN_LIMIT)
        {
            BooleMonomial mon=it->lead();
            auto v = *(mon.begin());
            if(ring.getVariableName(v)[0]=='L')
            {
                int i,j,k;
                sscanf(ring.getVariableName(v),"L_%d_%d_%d",&i,&j,&k);
                T[i][j][k] += *it;
                //cout<<L[i][j][k]<<","<<*it<<endl;
            }
        }
    }
    
	for(int i=0;i<Nr;i++)
	{
		for(int j=0;j<Nm;j++)
		{
			for(int k=0;k<64;k++)
			{
				TT[j][k] += Stt[16+k];
            }
            auto it_x= TT[j].begin();
            auto it_y= T[j][i].begin();
            for(int k=0;k<16;k++){
                vector<BoolePolynomial> ee = SboxAdd(vector<BoolePolynomial>(it_x,it_x+4),vector<BoolePolynomial>(it_y,it_y+4));
                for(unsigned int jj=0;jj<ee.size();jj++)
                {
                    if(!ignore_set[ToIgnoreSboxIndex(j,i,k,jj)])
                        eqs.push_back(ee[jj]);
                }
                it_x+=4;
                it_y+=4;
            }
            TT[j]=PBox(T[j][i]);
        }
        PrsKeyRoundEqsMQ(eqs,i,Stt);
	}
    
    for(int j=0;j<Nm;j++)
    {
        for(int k=0;k<64;k++)
        {
            TT[j][k] += Stt[16+k];
            TT[j][k] += Y[j][k];
        }
        move(TT[j].begin(),TT[j].end(),inserter(eqs,eqs.end()));
    }
}
