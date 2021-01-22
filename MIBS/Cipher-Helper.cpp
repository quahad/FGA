//============================================================================
// Name        : Mibs-Num-Helper.cpp
// Author      : 
// Version     :
// Copyright   : Your copyright notice
// Description : Hello World in C++, Ansi-style
//============================================================================

#include <polybori/polybori.h>

using namespace std;
using namespace polybori;

#define INT_TYPE            __uint32_t
#define INT_BIT_SIZE        32
#define CIPHER_STRING       "MIBS80"
#define STRATEGY    		CHOSEN_PLAINTEXT
#define KEY_GUESS_STRATEGY  WRONG_KEY_GUESS
#define GUESS_BITS          0
#define CONSIDER_KEY_VARS 	true
#define CUBE_LIKE_SAMPLES   false
#define PRINT_KEY   		false
#define CHECK_ENCRYPT_EQS   false
#define REPORT_GROBNER      false
#define REPORT_PRONE        false
#define FORWARD_ONLY        false
#define POLYNOMIAL_ANALYSIS false
#define NUM_SBOX_EQS        8


const int NumTest = 10;
const int Nr = 7;
const int Nm = 512;

const int KeySize = 80;
const int KeySchedSize = 80+8*32;
const int NumKeys = 80+8*Nr;
const int NumVars = NumKeys + Nm*Nr*32;

const vector<int> patt = { 0,1,2,3,4,5,6,7,8,9,10,11};
//vector<int> patt = { 32,33,34,35,36,37,38,39};
BoolePolyRing ring(NumVars,CTypes::dp_asc);
vector<BooleVariable> var_Keys(NumKeys,ring);
vector< vector< vector<BooleVariable> > > var_L(Nm,vector< vector<BooleVariable> >(Nr,vector<BooleVariable>(32,ring)));

vector<string> str_Keys(NumKeys);
vector< vector< array<string,32> > > str_L(Nm);

__uint64_t ToStateXY(__uint64_t x){
    return x;
}

__uint32_t ToStateI(__uint32_t x){
    return x;
}

#define LIN_ANALYSIS_START_ROUND 1
#define LIN_ANALYSIS_LAST_ROUND  (Nr-2)


                       
#include "../shared.h"

vector<BoolePolynomial> MibsBoxAddFWBW(const vector<BoolePolynomial>& X, const vector<BoolePolynomial>& Y)
{
	vector<BoolePolynomial> v(8,ring);
		v[0] = X[0] + Y[0]*Y[1]*Y[2] + Y[0]*Y[1] + Y[0]*Y[3] + Y[0] + Y[1]*Y[2]*Y[3] + Y[1]*Y[3] + Y[1] + Y[2] + 1;
		v[1] = X[1] + Y[0]*Y[1]*Y[3] + Y[0]*Y[1] + Y[0]*Y[2]*Y[3] + Y[1]*Y[2] + Y[1] + Y[2]*Y[3] + Y[2] + 1; 
		v[2] = X[2] + Y[0]*Y[1]*Y[3] + Y[0]*Y[1] + Y[0]*Y[2]*Y[3] + Y[0]*Y[3] + Y[1]*Y[2]*Y[3] + Y[1]*Y[2] + Y[1]*Y[3] + Y[2] + Y[3] + 1;
		v[3] = X[3] + Y[0]*Y[1]*Y[2] + Y[0]*Y[2]*Y[3] + Y[0] + Y[1]*Y[2]*Y[3] + Y[1]*Y[3] + Y[1];
		v[4] = Y[0] + X[0]*X[1]*X[2] + X[0]*X[1]*X[3] + X[0]*X[3] + X[0] + X[1]*X[2]*X[3] + X[1]*X[3] + X[1] + X[2] + X[3];
		v[5] = Y[1] + X[0]*X[1]*X[2] + X[0]*X[1]*X[3] + X[0]*X[2]*X[3] + X[0] + X[1]*X[2] + X[1]*X[3] + X[1] + X[3];
		v[6] = Y[2] + X[0]*X[1]*X[3] + X[0]*X[2]*X[3] + X[0]*X[2] + X[0]*X[3] + X[1]*X[2] + X[1] + X[3] + 1; 
		v[7] = Y[3] + X[0]*X[1]*X[2] + X[0]*X[2] + X[0] + X[1]*X[2]*X[3] + X[1]*X[3] + X[2] + X[3];

	return v;

}

vector<BoolePolynomial> SboxAdd(const vector<BoolePolynomial>& X, const vector<BoolePolynomial>& Y,int idx)
{
	return MibsBoxAddFWBW(X,Y);

}

vector<BoolePolynomial> MibsLin(const vector<BoolePolynomial>& X)
{
	vector<BoolePolynomial> T(32,ring);
	for(int i=0;i<4;i++)
	{
	    T[7*4+i] = X[6*4+i]+X[5*4+i]+X[4*4+i]+X[3*4+i]+X[2*4+i]+X[1*4+i];
	    T[6*4+i] = X[7*4+i]+X[5*4+i]+X[4*4+i]+X[2*4+i]+X[1*4+i]+X[0*4+i];
	    T[5*4+i] = X[7*4+i]+X[6*4+i]+X[4*4+i]+X[3*4+i]+X[1*4+i]+X[0*4+i];
	    T[4*4+i] = X[7*4+i]+X[6*4+i]+X[5*4+i]+X[3*4+i]+X[2*4+i]+X[0*4+i];
	    T[3*4+i] = X[7*4+i]+X[6*4+i]+X[4*4+i]+X[3*4+i]+X[2*4+i];
	    T[2*4+i] = X[7*4+i]+X[6*4+i]+X[5*4+i]+X[2*4+i]+X[1*4+i];
	    T[1*4+i] = X[6*4+i]+X[5*4+i]+X[4*4+i]+X[1*4+i]+X[0*4+i];
	    T[0*4+i] = X[7*4+i]+X[5*4+i]+X[4*4+i]+X[3*4+i]+X[0*4+i];
	}
	return T;
}

vector<BoolePolynomial> MibsInvLin(const vector<BoolePolynomial>& X)
{
	vector<BoolePolynomial> T(32,ring);
	for(int i=0;i<4;i++)
	{
	    T[7*4+i] = X[7*4+i]+X[6*4+i]+X[3*4+i]+X[2*4+i]+X[1*4+i];
	    T[6*4+i] = X[6*4+i]+X[5*4+i]+X[2*4+i]+X[1*4+i]+X[0*4+i];
	    T[5*4+i] = X[5*4+i]+X[4*4+i]+X[3*4+i]+X[1*4+i]+X[0*4+i];
	    T[4*4+i] = X[7*4+i]+X[4*4+i]+X[3*4+i]+X[2*4+i]+X[0*4+i];
	    T[3*4+i] = X[7*4+i]+X[6*4+i]+X[4*4+i]+X[2*4+i]+X[1*4+i]+X[0*4+i];
	    T[2*4+i] = X[7*4+i]+X[6*4+i]+X[5*4+i]+X[3*4+i]+X[1*4+i]+X[0*4+i];
	    T[1*4+i] = X[6*4+i]+X[5*4+i]+X[4*4+i]+X[3*4+i]+X[2*4+i]+X[0*4+i];
	    T[0*4+i] = X[7*4+i]+X[5*4+i]+X[4*4+i]+X[3*4+i]+X[2*4+i]+X[1*4+i];
	}
	return T;
}

vector<BoolePolynomial> MibsPerm(const vector<BoolePolynomial>& X)
{
	vector<BoolePolynomial> T(32,ring);
	for(int i=0;i<4;i++)
	{
	    T[6*4+i] = X[7*4+i];
	    T[0*4+i] = X[6*4+i];
	    T[7*4+i] = X[5*4+i];
	    T[5*4+i] = X[4*4+i];
	    T[2*4+i] = X[3*4+i];
	    T[1*4+i] = X[2*4+i];
	    T[4*4+i] = X[1*4+i];
	    T[3*4+i] = X[0*4+i];
	}
	return T;
}

vector<BoolePolynomial> MibsInvPerm(const vector<BoolePolynomial>& X)
{
	vector<BoolePolynomial> T(32,ring);
	for(int i=0;i<4;i++)
	{
	    T[7*4+i] = X[6*4+i];
	    T[6*4+i] = X[0*4+i];
	    T[5*4+i] = X[7*4+i];
	    T[4*4+i] = X[5*4+i];
	    T[3*4+i] = X[2*4+i];
	    T[2*4+i] = X[1*4+i];
	    T[1*4+i] = X[4*4+i];
	    T[0*4+i] = X[3*4+i];
	}
	return T;
}


void MibsKeyRoundEqsMQ(vector<BoolePolynomial>& keqs,int rnd,vector<BoolePolynomial>& Stt)
{
	vector<BoolePolynomial> T(80,ring);
	for(int i=0;i<80;i++)
		T[i] = Stt[(i+19)%80];
	auto it_T=T.begin();
	auto it_k =var_Keys.begin();

	vector<BoolePolynomial> ee = SboxAdd(vector<BoolePolynomial>(it_T+76,it_T+80),vector<BoolePolynomial>(it_k+80+rnd*8+4,it_k+80+rnd*8+8));
	move(ee.begin(),ee.end(),inserter(keqs,keqs.end()));
	ee = SboxAdd(vector<BoolePolynomial>(it_T+72,it_T+76),vector<BoolePolynomial>(it_k+80+rnd*8+0,it_k+80+rnd*8+4));
	move(ee.begin(),ee.end(),inserter(keqs,keqs.end()));
	for(int i=0;i<8;i++)
		T[72+i] = var_Keys[80+rnd*8+i];
	for(int i=0;i<5;i++)
		T[14+i] += (((rnd+1)>>i)&0x1);
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
    vector<BoolePolynomial> derived_polys;
	vector< vector< vector<BoolePolynomial> > > L(Nm,vector< vector<BoolePolynomial> >(Nr+2,vector<BoolePolynomial>(32,ring)));
	for(int i=0;i<Nm;i++)
	{
		for(int j=0;j<32;j++)
		{
			L[i][0][j] = X[i][j];
			L[i][1][j] = X[i][32+j];
			L[i][Nr][j] = Y[i][32+j];
			L[i][Nr+1][j] = Y[i][j];
		}
		for(int j=1;j<Nr-1;j++)
		{
			for(int k=0;k<32;k++)
			{
				L[i][j+1][k] = var_L[i][j][k];
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
                L[i][j+1][k] += *it;
                //cout<<L[i][j+1][k]<<","<<*it<<endl;
            }
        }
    }
    

	for(int i=0;i<Nr;i++)
	{
		vector<BoolePolynomial> rk(32,ring);
        MibsKeyRoundEqsMQ(eqs,i,Stt);
		for(int k=0;k<32;k++)
			rk[k] = Stt[48+k];
		for(int j=0;j<Nm;j++)
		{
			vector<BoolePolynomial> tt= rk;
            vector<BoolePolynomial> t = L[j][i];
			for(int k=0;k<32;k++)
			{
				tt[k] += L[j][i+1][k];
                t[k] += L[j][i+2][k];
			}
			t = MibsInvPerm(t);
            t = MibsInvLin(t);
            auto it_x= tt.begin();
            auto it_y= t.begin();
            for(int k=0;k<8;k++){
                vector<BoolePolynomial> ee = SboxAdd(vector<BoolePolynomial>(it_x,it_x+4),vector<BoolePolynomial>(it_y,it_y+4));
                for(int jj=0;jj<ee.size();jj++)
                {
                    if(!ee[jj].isZero() && !ignore_set[ToIgnoreSboxIndex(j,i,k,jj)])
                        eqs.push_back(ee[jj]);
                }
                it_x+=4;
                it_y+=4;
            }
        }
        //if(i < ((Nr+1)/2))
        //    eqs = interred(eqs);
            
	}
    
}
