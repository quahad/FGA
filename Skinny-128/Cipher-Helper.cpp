//============================================================================
// Name        : Skinny-128-Num-Helper.cpp
// Author      :
// Version     :
// Copyright   : Your copyright notice
// Description : Hello World in C++, Ansi-style
//============================================================================

#include <polybori/polybori.h>

using namespace std;
using namespace polybori;

#define INT_TYPE 		__uint64_t
#define INT_BIT_SIZE 		64
#define CIPHER_STRING   	"SKINNY128"
#define STRATEGY    		KNOWN_CIPHERTEXT
#define GUESS_BITS          0
#define KEY_GUESS_STRATEGY  RIGHT_KEY_GUESS
#define CONSIDER_KEY_VARS 	true
#define PRINT_KEY   		false
#define CUBE_LIKE_SAMPLES   true
#define REPORT_PRONE        false
#define REPORT_GROBNER 		false
#define CHECK_ENCRYPT_EQS   false
#define POLYNOMIAL_ANALYSIS false
#define FORWARD_ONLY        false
#define NUM_SBOX_EQS        8



const int NumTest = 10;
const int Nr = 6;
const int Nm = 256;
const int KeySize = 128;
const int KeySchedSize = 128;
const int NumKeys = KeySchedSize;
const int NumVars = NumKeys + Nm*Nr*64;


vector<int> patt = { 0,1,2,3,4,5,6,7,8,9,10,11};
//vector<int> patt = { 8,9,10,11,12,13,14,15};
//vector<int> patt = { 28,29,30,31,44,45,46,47,48};
//vector<int> patt = { 20, 21, 22, 23, 28, 29, 30, 31, 44, 45, 46, 47};
//vector<int> patt = { 0, 1, 2, 3, 32};
BoolePolyRing ring(NumVars,CTypes::block_dp_asc);
vector<BooleVariable> var_Keys(NumKeys,ring);
vector< vector< vector<BooleVariable> > > var_L(Nm,vector< vector<BooleVariable> >(Nr,vector<BooleVariable>(64,ring)));

vector<string> str_Keys(NumKeys);
vector< vector< array<string,64> > > str_L(Nm);



uint64_t ToStateXY(uint64_t X)
{
    uint64_t T=0;
    for(int i=0;i<16;i++)
    {
        T<<=4;
        T^=(X>>4*i)&0xF;
    }
    return T;
}

uint64_t ToStateI(uint64_t X)
{
    uint64_t T=0;
    for(int i=0;i<16;i++)
    {
        T<<=4;
        T^=(X>>4*i)&0xF;
    }
    return T;
}



#define LIN_ANALYSIS_START_ROUND 0
#define LIN_ANALYSIS_LAST_ROUND  (Nr-1)


#include "../shared.h"




vector<BoolePolynomial> SkBoxAddFWBW(const vector<BoolePolynomial>& X, const vector<BoolePolynomial>& Y)
{
	vector<BoolePolynomial> vv{ Y[0]+X[0]*X[1]*X[2] + X[0]*X[1] + X[0]*X[2] + X[0]*X[3] + X[1]*X[2]*X[3] + X[1]*X[3] + X[1] + X[2] + X[3],
                                Y[1]+X[0]*X[1] + X[0] + X[1]*X[2]*X[3] + X[1]*X[2] + X[1]*X[3] + X[2]*X[3] + X[3],
                                Y[2]+X[1]*X[2] + X[1] + X[2] + X[3] + 1,
                                Y[3]+X[0] + X[2]*X[3] + X[2] + X[3] + 1,
                                X[0] + Y[0]*Y[1] + Y[0]*Y[2]*Y[3] + Y[0]*Y[2] + Y[0] + Y[1]*Y[2]*Y[3] + Y[1]*Y[3] + Y[1] + Y[2] + 1,
                                X[1] + Y[0] + Y[2]*Y[3] + Y[2] + Y[3] + 1,
                                X[2] + Y[0]*Y[3] + Y[0] + Y[1] + Y[2]*Y[3] + Y[2],
                                X[3] + Y[0]*Y[1] + Y[0]*Y[3] + Y[1]*Y[2]*Y[3] + Y[1]*Y[2] + Y[1]*Y[3] + Y[2] + Y[3]};
	return vv;
}

vector<BoolePolynomial> SboxAdd(const vector<BoolePolynomial>& X, const vector<BoolePolynomial>& Y, int idx)
{
	return SkBoxAddFWBW(X,Y);

}

const uint8_t PT[] = {9,15,8,13,10,14,12,11,0,1,2,3,4,5,6,7};
const uint8_t PS[] = {0,1,2,3,7,4,5,6,10,11,8,9,13,14,15,12};
const uint8_t RC[] ={0x01, 0x03, 0x07, 0x0F, 0x1F, 0x3E, 0x3D, 0x3B, 0x37, 0x2F,
	0x1E, 0x3C, 0x39, 0x33, 0x27, 0x0E, 0x1D, 0x3A, 0x35, 0x2B,
	0x16, 0x2C, 0x18, 0x30, 0x21, 0x02, 0x05, 0x0B, 0x17, 0x2E,
	0x1C, 0x38, 0x31, 0x23, 0x06, 0x0D, 0x1B, 0x36, 0x2D, 0x1A,
	0x34, 0x29, 0x12, 0x24, 0x08, 0x11, 0x22, 0x04, 0x09, 0x13,
	0x26, 0x0c, 0x19, 0x32, 0x25, 0x0a, 0x15, 0x2a, 0x14, 0x28,
	0x10, 0x20};
vector<BoolePolynomial> SkPermT(const vector<BoolePolynomial>& X)
{
	vector<BoolePolynomial> T(64,ring);
	for(int i=0;i<4;i++)
	{
        for(int j=0;j<16;j++)
            T[j*4+i] = X[PT[j]*4+i];
	}
	return T;
}

vector<BoolePolynomial> SkShiftRow(const vector<BoolePolynomial>& X)
{
	vector<BoolePolynomial> T(64,ring);
	for(int i=0;i<4;i++)
	{
        for(int j=0;j<16;j++)
            T[j*4+i] = X[PS[j]*4+i];
	}
	return T;
}

vector<BoolePolynomial> SkAddConstants(const vector<BoolePolynomial>& X, int r)
{
	vector<BoolePolynomial> T=X;
	for(int i=0;i<4;i++)
	{
        T[0*4+i] += ((RC[r]>>(i))&0x1);
        T[4*4+i] += ((RC[r]>>(i+4))&0x1);
        T[8*4+i] += (((0x2)>>(i))&0x1);
	}
    /*for(auto it=T.begin();it!=T.end();it++)
        cout<<*it<<",";
    cout<<endl;*/
	return T;
}

vector<BoolePolynomial> SkMixColumn(const vector<BoolePolynomial>& T)
{
	vector<BoolePolynomial> X=T;
	for(int i=0;i<4;i++)
	{
        for(int j=0;j<4;j++)
        {
            X[(1*4+j)*4+i] += X[(2*4+j)*4+i];
            X[(2*4+j)*4+i] += X[(0*4+j)*4+i];
            X[(3*4+j)*4+i] += X[(2*4+j)*4+i];
            auto temp = X[(3*4+j)*4+i];
            X[(3*4+j)*4+i] = X[(2*4+j)*4+i];
            X[(2*4+j)*4+i] = X[(1*4+j)*4+i];
            X[(1*4+j)*4+i] = X[(0*4+j)*4+i];
            X[(0*4+j)*4+i] = temp;
        }
	}
	return X;
}



void AIOEncryptEqs(vector<BoolePolynomial>& eqs,
                       const vector<BoolePolynomial>& forward_eqs,
                       const bitset<IGNORE_BITSET_SIZE>& ignore_set,
                       const vector<BoolePolynomial>& K,
                       const vector< vector<BoolePolynomial> >& X,
                       const vector< vector<BoolePolynomial> >& Y)

{
	vector<BoolePolynomial> TK0(64,ring);
    vector<BoolePolynomial> TK1(64,ring);

    for(int i=0;i<16;i++)
        for(int j=0;j<4;j++)
            TK0[(15-i)*4+j] = K[(16+i)*4+j];

    for(int i=0;i<16;i++)
    {
        for(int j=0;j<4;j++)
            TK1[(15-i)*4+j] = K[i*4+j];
    }

	vector< vector<BoolePolynomial> > S=X;
	vector< vector< vector<BoolePolynomial> > > L(Nm,vector< vector<BoolePolynomial> >(Nr,vector<BoolePolynomial>(64,ring)));
	for(int i=0;i<Nm;i++)
	{
		for(int j=0;j<Nr;j++)
		{
			for(int k=0;k<64;k++)
			{
				L[i][j][k] = var_L[i][j][k];
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
                L[i][j][k] += *it;
                //cout<<L[i][j][k]<<","<<*it<<endl;
            }
        }
    }

	for(int i=0;i<Nr;i++)
	{
        //cout<<i<<endl;
        vector<BoolePolynomial> cc;
		for(int j=0;j<Nm;j++)
		{
            //Apply SubCell
            auto it_x= S[j].begin();
            auto it_y= L[j][i].begin();
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
            S[j] = L[j][i];
            S[j]=SkAddConstants(S[j],i);
            //AddTweak
            for(int k=0;k<32;k++)
            {
                S[j][k]+=TK0[k]+TK1[k];
            }
            S[j]=SkShiftRow(S[j]);
            S[j]=SkMixColumn(S[j]);
		}
        //cc=interred(cc);
        move(cc.begin(),cc.end(),inserter(eqs,eqs.end()));
        //Update Tweak
        TK0=SkPermT(TK0);
        TK1=SkPermT(TK1);
        //Update TK1 with LFSR
        for(int j=0;j<8;j++)
        {
            BoolePolynomial w0 = TK1[j*4+0],
                            w1 = TK1[j*4+1],
                            w2 = TK1[j*4+2],
                            w3 = TK1[j*4+3];
            TK1[j*4+0] = w3+w2;
            TK1[j*4+1] = w0;
            TK1[j*4+2] = w1;
            TK1[j*4+3] = w2;

        }
	}
    for(int i=0;i<Nm;i++)
    {
        for(int j=0;j<64;j++)
        {
            S[i][j]+=Y[i][j];
            eqs.push_back(S[i][j]);
        }
     }
}
