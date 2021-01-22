//============================================================================
// Name        : Lblock-Num-Helper.cpp
// Author      :
// Version     :
// Copyright   : Your copyright notice
// Description : Hello World in C++, Ansi-style
//============================================================================

#include <polybori/polybori.h>

using namespace std;
using namespace polybori;

#define INT_TYPE __uint32_t
#define INT_BIT_SIZE 32
#define CIPHER_STRING "LBlock80"
#define STRATEGY CHOSEN_PLAINTEXT
#define GUESS_BITS 0
#define KEY_GUESS_STRATEGY RIGHT_KEY_GUESS
#define REPORT_GROBNER false
#define CONSIDER_KEY_VARS false
#define PRINT_KEY false
#define CUBE_LIKE_SAMPLES true
#define REPORT_PRONE false
#define CHECK_ENCRYPT_EQS false
#define FORWARD_ONLY false
#define POLYNOMIAL_ANALYSIS false
#define NUM_SBOX_EQS 8

const int NumTest = 10;
const int Nr = 8;
const int Nm = 4;
const int KeySize = 80;
const int KeySchedSize = 80 + 8 * 31;
const int NumKeys = 80 + 8 * (Nr - 1);
const int NumVars = NumKeys + Nm * (Nr - 2) * 32;

vector<int> patt = {0, 1, 2, 3, 32, 33, 34, 35, 24, 25, 26, 27};
//vector<int> patt = { 8,9,10,11,12,13,14,15};
//vector<int> patt = { 28,29,30,31,44,45,46,47,48};
//vector<int> patt = { 20, 21, 22, 23, 28, 29, 30, 31, 44, 45, 46, 47};
//vector<int> patt = { 0, 1, 2, 3, 32};
BoolePolyRing ring(NumVars, CTypes::dp_asc);
vector<BooleVariable> var_Keys(NumKeys, ring);
vector<vector<vector<BooleVariable>>> var_L(Nm, vector<vector<BooleVariable>>(Nr, vector<BooleVariable>(32, ring)));

vector<string> str_Keys(NumKeys);
vector<vector<array<string, 32>>> str_L(Nm);

__uint64_t ToStateXY(__uint64_t x)
{
    return x;
}

__uint32_t ToStateI(__uint32_t x)
{
    return x;
}

#define LIN_ANALYSIS_START_ROUND 1
#define LIN_ANALYSIS_LAST_ROUND (Nr - 2)

#include "../shared.h"

vector<BoolePolynomial> LbBoxAddFWBW(const vector<BoolePolynomial> &X, const vector<BoolePolynomial> &Y, const int i)
{
    vector<BoolePolynomial> v(8, ring);
    switch (i)
    {
    case 0:
        v[0] = Y[0] + X[0] + X[1] + X[2] * X[3] + X[2] + X[3];
        v[1] = Y[1] + X[0] * X[2] + X[0] + X[1] * X[2] + X[2] + X[3] + 1;
        v[2] = Y[2] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] * X[3] + X[0] + X[1] * X[2] * X[3] + X[1] * X[2] + X[2] * X[3] + X[3] + 1;
        v[3] = Y[3] + X[0] * X[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[1] * X[3] + X[3] + 1;
        v[4] = X[0] + Y[0] * Y[1] * Y[3] + Y[0] * Y[1] + Y[0] * Y[2] + Y[0] + Y[3] + 1;
        v[5] = X[1] + Y[0] * Y[1] * Y[2] + Y[0] * Y[1] * Y[3] + Y[0] + Y[1] * Y[2] + Y[1] * Y[3] + Y[1] + Y[2] * Y[3] + Y[2] + 1;
        v[6] = X[2] + Y[1] * Y[3] + Y[2];
        v[7] = X[3] + Y[0] * Y[1] + Y[0] + Y[1] + Y[3];
        break;
    case 1:
        v[0] = Y[0] + X[0] * X[2] + X[0] + X[1] * X[2] + X[2] + X[3];
        v[1] = Y[1] + X[0] + X[1] + X[2] * X[3] + X[2] + X[3];
        v[2] = Y[2] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] * X[3] + X[0] + X[1] * X[2] * X[3] + X[1] * X[2] + X[2] * X[3] + 1;
        v[3] = Y[3] + X[0] * X[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] + X[1] * X[3] + X[1] + X[2] * X[3] + X[2];
        v[4] = X[0] + Y[0] * Y[1] * Y[3] + Y[0] * Y[1] + Y[1] * Y[2] + Y[3];
        v[5] = X[1] + Y[0] * Y[1] * Y[2] + Y[0] * Y[1] * Y[3] + Y[0] * Y[1] + Y[0] * Y[2] + Y[0] * Y[3] + Y[1] + Y[2] * Y[3] + Y[2] + Y[3] + 1;
        v[6] = X[2] + Y[0] * Y[3] + Y[2] + 1;
        v[7] = X[3] + Y[0] * Y[1] + Y[0] + Y[1] + Y[3];
        break;
    case 2:
        v[0] = Y[0] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] * X[3] + X[0] + X[1] * X[2] * X[3] + X[1] * X[2] + X[2] * X[3] + 1;
        v[1] = Y[1] + X[0] + X[1] + X[2] * X[3] + X[2] + X[3];
        v[2] = Y[2] + X[0] * X[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] + X[1] * X[3] + X[1] + X[2] * X[3] + X[2];
        v[3] = Y[3] + X[0] * X[2] + X[0] + X[1] * X[2] + X[2] + X[3];
        v[4] = X[0] + Y[0] * Y[1] + Y[1] * Y[2] * Y[3] + Y[1] * Y[3] + Y[2];
        v[5] = X[1] + Y[0] * Y[1] * Y[3] + Y[0] * Y[2] + Y[0] * Y[3] + Y[0] + Y[1] * Y[2] * Y[3] + Y[1] * Y[3] + Y[1] + Y[2] * Y[3] + Y[2] + 1;
        v[6] = X[2] + Y[0] + Y[2] * Y[3] + 1;
        v[7] = X[3] + Y[1] * Y[3] + Y[1] + Y[2] + Y[3];
        break;
    case 3:
        v[0] = Y[0] + X[0] + X[1] + X[2] * X[3] + X[2] + 1;
        v[1] = Y[1] + X[0] * X[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] * X[3] + X[1] * X[3] + X[1] + X[2] * X[3] + X[2] + X[3] + 1;
        v[2] = Y[2] + X[0] * X[2] + X[1] * X[2] + X[1] + X[2] + X[3] + 1;
        v[3] = Y[3] + X[0] * X[2] * X[3] + X[0] * X[2] + X[1] * X[2] * X[3] + X[1] * X[2] + X[1] * X[3] + X[1] + X[2] * X[3] + X[3];
        v[4] = X[0] + Y[0] * Y[1] * Y[2] + Y[0] * Y[2] + Y[0] * Y[3] + Y[0] + Y[1];
        v[5] = X[1] + Y[0] * Y[1] * Y[2] + Y[0] * Y[2] * Y[3] + Y[0] + Y[1] * Y[2] + Y[1] * Y[3] + Y[2] * Y[3] + Y[2] + Y[3];
        v[6] = X[2] + Y[1] * Y[2] + Y[3] + 1;
        v[7] = X[3] + Y[0] * Y[2] + Y[0] + Y[1] + Y[2];
        break;
    case 4:
        v[0] = Y[0] + X[0] + X[1] + X[2] * X[3] + X[2] + X[3];
        v[1] = Y[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] * X[3] + X[0] + X[1] * X[2] * X[3] + X[1] * X[2] + X[2] * X[3] + X[3] + 1;
        v[2] = Y[2] + X[0] * X[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[1] * X[3] + X[3] + 1;
        v[3] = Y[3] + X[0] * X[2] + X[0] + X[1] * X[2] + X[2] + X[3] + 1;
        v[4] = X[0] + Y[0] * Y[1] + Y[0] * Y[2] * Y[3] + Y[0] * Y[3] + Y[0] + Y[2] + 1;
        v[5] = X[1] + Y[0] * Y[1] * Y[3] + Y[0] * Y[2] * Y[3] + Y[0] + Y[1] * Y[2] + Y[1] * Y[3] + Y[1] + Y[2] * Y[3] + Y[3] + 1;
        v[6] = X[2] + Y[1] + Y[2] * Y[3];
        v[7] = X[3] + Y[0] * Y[3] + Y[0] + Y[2] + Y[3];
        break;
    case 5:
        v[0] = Y[0] + X[0] + X[1] + X[2] * X[3] + X[2] + X[3];
        v[1] = Y[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] * X[3] + X[0] + X[1] * X[2] * X[3] + X[1] * X[2] + X[2] * X[3] + 1;
        v[2] = Y[2] + X[0] * X[2] + X[0] + X[1] * X[2] + X[2] + X[3];
        v[3] = Y[3] + X[0] * X[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] + X[1] * X[3] + X[1] + X[2] * X[3] + X[2];
        v[4] = X[0] + Y[0] * Y[1] + Y[0] * Y[2] * Y[3] + Y[0] * Y[2] + Y[3];
        v[5] = X[1] + Y[0] * Y[1] * Y[2] + Y[0] * Y[2] * Y[3] + Y[0] * Y[2] + Y[0] + Y[1] * Y[2] + Y[1] * Y[3] + Y[1] + Y[2] * Y[3] + Y[3] + 1;
        v[6] = X[2] + Y[1] + Y[2] * Y[3] + 1;
        v[7] = X[3] + Y[0] * Y[2] + Y[0] + Y[2] + Y[3];
        break;
    case 6:
        v[0] = Y[0] + X[0] * X[2] + X[1] * X[2] + X[1] + X[2] + X[3] + 1;
        v[1] = Y[1] + X[0] + X[1] + X[2] * X[3] + X[2] + 1;
        v[2] = Y[2] + X[0] * X[2] * X[3] + X[0] * X[2] + X[1] * X[2] * X[3] + X[1] * X[2] + X[1] * X[3] + X[1] + X[2] * X[3] + X[3];
        v[3] = Y[3] + X[0] * X[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] * X[3] + X[1] * X[3] + X[1] + X[2] * X[3] + X[2] + X[3] + 1;
        v[4] = X[0] + Y[0] * Y[1] * Y[3] + Y[0] * Y[1] + Y[1] * Y[2] + Y[1] + Y[3];
        v[5] = X[1] + Y[0] * Y[1] * Y[2] + Y[0] * Y[1] * Y[3] + Y[0] * Y[2] + Y[0] * Y[3] + Y[0] + Y[1] + Y[2] * Y[3] + Y[2];
        v[6] = X[2] + Y[0] * Y[3] + Y[2] + 1;
        v[7] = X[3] + Y[0] * Y[1] + Y[0] + Y[1] + Y[3];
        break;
    case 7:
        v[0] = Y[0] + X[0] * X[2] + X[0] + X[1] * X[2] + X[2] + X[3] + 1;
        v[1] = Y[1] + X[0] + X[1] + X[2] * X[3] + X[2] + X[3];
        v[2] = Y[2] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] * X[3] + X[0] + X[1] * X[2] * X[3] + X[1] * X[2] + X[2] * X[3] + X[3] + 1;
        v[3] = Y[3] + X[0] * X[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[1] * X[3] + X[3] + 1;
        v[4] = X[0] + Y[0] * Y[1] * Y[3] + Y[0] * Y[1] + Y[1] * Y[2] + Y[1] + Y[3] + 1;
        v[5] = X[1] + Y[0] * Y[1] * Y[2] + Y[0] * Y[1] * Y[3] + Y[0] * Y[2] + Y[0] * Y[3] + Y[0] + Y[1] + Y[2] * Y[3] + Y[2] + 1;
        v[6] = X[2] + Y[0] * Y[3] + Y[2];
        v[7] = X[3] + Y[0] * Y[1] + Y[0] + Y[1] + Y[3];
        break;

    case 8:
        v[0] = Y[0] + X[0] * X[2] + X[0] + X[1] * X[2] + X[2] + X[3];
        v[1] = Y[1] + X[0] + X[1] + X[2] * X[3] + X[2] + X[3];
        v[2] = Y[2] + X[0] * X[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] + X[1] * X[3] + X[1] + X[2] * X[3] + X[2];
        v[3] = Y[3] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] * X[3] + X[0] + X[1] * X[2] * X[3] + X[1] * X[2] + X[2] * X[3] + 1;
        v[4] = X[0] + Y[0] * Y[1] * Y[2] + Y[0] * Y[1] + Y[1] * Y[3] + Y[2];
        v[5] = X[1] + Y[0] * Y[1] * Y[2] + Y[0] * Y[1] * Y[3] + Y[0] * Y[1] + Y[0] * Y[2] + Y[0] * Y[3] + Y[1] + Y[2] * Y[3] + Y[2] + Y[3] + 1;
        v[6] = X[2] + Y[0] * Y[2] + Y[3] + 1;
        v[7] = X[3] + Y[0] * Y[1] + Y[0] + Y[1] + Y[2];
        break;

    case 9:
        v[0] = Y[0] + X[0] * X[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[1] * X[3] + X[3] + 1;
        v[1] = Y[1] + X[0] * X[2] * X[3] + X[0] * X[2] + X[0] * X[3] + X[0] + X[1] * X[2] * X[3] + X[1] * X[2] + X[2] * X[3] + X[3] + 1;
        v[2] = Y[2] + X[0] + X[1] + X[2] * X[3] + X[2] + X[3];
        v[3] = Y[3] + X[0] * X[2] + X[0] + X[1] * X[2] + X[2] + X[3] + 1;
        v[4] = X[0] + Y[0] * Y[2] * Y[3] + Y[0] + Y[1] * Y[2] + Y[2] * Y[3] + Y[2] + 1;
        v[5] = X[1] + Y[0] * Y[1] + Y[0] * Y[2] * Y[3] + Y[0] * Y[3] + Y[1] * Y[2] * Y[3] + Y[1] * Y[3] + Y[1] + Y[2] + Y[3] + 1;
        v[6] = X[2] + Y[0] * Y[3] + Y[1];
        v[7] = X[3] + Y[0] + Y[2] * Y[3] + Y[2] + Y[3];
        break;
    }
    return v;
}

vector<BoolePolynomial> LbBoxAddMQ(const vector<BoolePolynomial> &X, const vector<BoolePolynomial> &Y, const int i)
{
    if (i == 0)
    {
        vector<BoolePolynomial> vv{Y[2] * Y[3] + X[0] * Y[1] + X[0] * X[2] + Y[1] + X[2], Y[1] * Y[3] + Y[2] + X[2], Y[1] * Y[2] + X[0] * X[2] + Y[2] + Y[1] + Y[0] + X[2] + X[1] + 1, Y[0] * Y[3] + X[0] * Y[0] + Y[3] + Y[0] + X[0] + 1, Y[0] * Y[2] + X[0] * Y[3] + X[0] * Y[0] + X[0] * X[3] + Y[3] + Y[2] + Y[1] + Y[0] + X[2] + X[0] + 1, Y[0] * Y[1] + Y[3] + Y[1] + Y[0] + X[3], X[3] * Y[3] + X[0] * Y[3] + X[0] * X[3] + Y[3] + X[3] + X[0] + 1, X[3] * Y[2] + Y[0] + X[3] + X[2] + X[1] + X[0], X[3] * Y[1] + Y[2] + Y[1] + X[2], X[3] * Y[0] + X[0] * Y[0] + Y[3] + X[0] + 1, X[2] * Y[3] + X[0] * Y[1] + X[0] * X[2] + Y[2] + Y[1], X[2] * Y[2] + X[0] * Y[0] + X[0] * X[1] + Y[2] + Y[0] + X[1] + X[0] + 1, X[2] * Y[1] + X[0] * X[2] + Y[1] + Y[0] + X[1] + 1, X[2] * Y[0] + Y[1] + X[3] + X[0] + 1, X[2] * X[3] + Y[0] + X[3] + X[2] + X[1] + X[0], X[1] * Y[3] + X[0] * Y[2] + X[0] * X[2] + X[0] * X[1] + X[1], X[1] * Y[2] + X[0] * Y[3] + X[0] * Y[2] + X[0] * X[3] + X[0] * X[1] + Y[3] + Y[1] + X[2] + X[1], X[1] * Y[1] + X[0] * Y[1] + X[0] * Y[0] + X[0] * X[1] + Y[3] + X[3] + X[1] + X[0] + 1, X[1] * Y[0] + X[0] * X[3] + Y[3] + Y[2] + Y[0] + X[3] + X[2], X[1] * X[3] + X[0] * Y[0] + X[0] * X[3] + Y[3] + X[3] + X[0] + 1, X[1] * X[2] + X[0] * X[2] + Y[1] + X[3] + X[2] + X[0] + 1};
        return vv;
    }
    if (i == 1)
    {
        vector<BoolePolynomial> vv{Y[2] * Y[3] + X[0] * Y[0] + X[0] * X[2] + Y[3], Y[1] * Y[3] + X[0] * Y[1] + Y[3] + X[0], Y[1] * Y[2] + X[0] * Y[3] + X[0] * Y[1] + X[0] * X[3] + Y[2] + Y[1] + Y[0] + X[3] + X[2] + X[0] + 1, Y[0] * Y[3] + Y[2] + X[2] + 1, Y[0] * Y[2] + X[0] * X[2] + Y[2] + Y[1] + X[1] + 1, Y[0] * Y[1] + Y[3] + Y[1] + Y[0] + X[3], X[3] * Y[3] + X[0] * Y[3] + X[0] * X[3] + X[0], X[3] * Y[2] + Y[1] + X[2] + X[1] + X[0], X[3] * Y[1] + X[0] * Y[1] + Y[3] + Y[1] + X[0], X[3] * Y[0] + Y[2] + Y[0] + X[2] + 1, X[2] * Y[3] + X[0] * Y[0] + X[0] * X[2] + Y[2] + X[2] + 1, X[2] * Y[2] + X[0] * Y[1] + X[0] * X[1] + Y[2] + X[2] + 1, X[2] * Y[1] + Y[0] + X[3] + X[0], X[2] * Y[0] + X[0] * X[2] + Y[1] + Y[0] + X[2] + X[1], X[2] * X[3] + Y[1] + X[3] + X[2] + X[1] + X[0], X[1] * Y[3] + X[0] * Y[2] + X[0] * X[2] + X[0] * X[1] + Y[3] + Y[2] + X[2] + 1, X[1] * Y[2] + X[0] * Y[3] + X[0] * Y[2] + X[0] * X[3] + X[0] * X[1] + Y[0] + X[3] + X[2] + X[1], X[1] * Y[1] + X[0] * X[3] + Y[3] + Y[2] + X[2] + 1, X[1] * Y[0] + X[0] * Y[1] + X[0] * Y[0] + X[0] * X[1] + Y[3] + Y[1] + X[3], X[1] * X[3] + X[0] * Y[1] + X[0] * X[3] + Y[3] + Y[1] + X[3] + X[0], X[1] * X[2] + X[0] * X[2] + Y[0] + X[3] + X[2] + X[0]};
        return vv;
    }
    if (i == 2)
    {
        vector<BoolePolynomial> vv{Y[2] * Y[3] + Y[0] + X[2] + 1, Y[1] * Y[3] + Y[3] + Y[2] + Y[1] + X[3], Y[1] * Y[2] + X[0] * Y[1] + Y[2] + X[0], Y[0] * Y[3] + X[0] * X[2] + Y[1] + Y[0] + X[1] + 1, Y[0] * Y[2] + X[0] * Y[3] + X[0] * X[2] + Y[2], Y[0] * Y[1] + X[0] * Y[2] + X[0] * Y[1] + X[0] * X[3] + Y[3] + Y[1] + Y[0] + X[3] + X[2] + X[0] + 1, X[3] * Y[3] + Y[3] + Y[0] + X[2] + 1, X[3] * Y[2] + X[0] * Y[2] + X[0] * X[3] + X[0], X[3] * Y[1] + X[0] * Y[1] + Y[2] + Y[1] + X[0], X[3] * Y[0] + Y[1] + X[2] + X[1] + X[0], X[2] * Y[3] + X[0] * X[2] + Y[3] + Y[1] + X[2] + X[1], X[2] * Y[2] + X[0] * Y[3] + X[0] * X[2] + Y[0] + X[2] + 1, X[2] * Y[1] + Y[3] + X[3] + X[0], X[2] * Y[0] + X[0] * Y[1] + X[0] * X[1] + Y[0] + X[2] + 1, X[2] * X[3] + Y[1] + X[3] + X[2] + X[1] + X[0], X[1] * Y[3] + X[0] * Y[3] + X[0] * Y[1] + X[0] * X[1] + Y[2] + Y[1] + X[3], X[1] * Y[2] + X[0] * Y[0] + X[0] * X[2] + X[0] * X[1] + Y[2] + Y[0] + X[2] + 1, X[1] * Y[1] + X[0] * X[3] + Y[2] + Y[0] + X[2] + 1, X[1] * Y[0] + X[0] * Y[2] + X[0] * Y[0] + X[0] * X[3] + X[0] * X[1] + Y[3] + X[3] + X[2] + X[1], X[1] * X[3] + X[0] * Y[1] + X[0] * X[3] + Y[2] + Y[1] + X[3] + X[0], X[1] * X[2] + X[0] * X[2] + Y[3] + X[3] + X[2] + X[0]};
        return vv;
    }
    if (i == 3)
    {
        vector<BoolePolynomial> vv{Y[2] * Y[3] + X[0] * X[2] + Y[3] + Y[2] + Y[0] + X[1] + X[0], Y[1] * Y[3] + X[0] * Y[2] + X[0] * X[2] + X[0], Y[1] * Y[2] + Y[3] + X[2] + 1, Y[0] * Y[3] + X[0] * Y[1] + X[0] * Y[0] + X[0] * X[3] + Y[3] + Y[2] + X[3] + X[2] + X[0] + 1, Y[0] * Y[2] + Y[2] + Y[1] + Y[0] + X[3], Y[0] * Y[1] + X[0] * Y[0] + Y[1] + X[0], X[3] * Y[3] + Y[0] + X[3] + X[2] + X[1] + X[0] + 1, X[3] * Y[2] + Y[3] + Y[2] + X[2] + 1, X[3] * Y[1] + X[0] * Y[1] + X[0] * X[3] + X[0], X[3] * Y[0] + X[0] * Y[0] + Y[1] + Y[0] + X[0], X[2] * Y[3] + X[0] * Y[0] + X[0] * X[1], X[2] * Y[2] + X[0] * X[2] + Y[0] + X[2] + X[1] + X[0] + 1, X[2] * Y[1] + X[0] * Y[2] + X[0] * X[2] + Y[3] + Y[1] + X[2] + X[0] + 1, X[2] * Y[0] + Y[2] + Y[0] + X[3] + X[0], X[2] * X[3] + Y[0] + X[2] + X[1] + X[0] + 1, X[1] * Y[3] + X[0] * Y[3] + X[0] * Y[1] + X[0] * X[3] + X[0] * X[1] + Y[2] + X[3] + X[2] + X[0] + 1, X[1] * Y[2] + X[0] * Y[2] + X[0] * Y[0] + X[0] * X[1] + Y[1] + Y[0] + X[3], X[1] * Y[1] + X[0] * Y[3] + X[0] * X[2] + X[0] * X[1] + Y[3] + Y[1] + X[2] + 1, X[1] * Y[0] + X[0] * X[3] + Y[3] + Y[1] + X[2] + 1, X[1] * X[3] + X[0] * Y[0] + X[0] * X[3] + Y[1] + Y[0] + X[3] + X[0], X[1] * X[2] + X[0] * X[2] + Y[2] + X[3] + X[2] + X[1] + 1};
        return vv;
    }
    if (i == 4)
    {
        vector<BoolePolynomial> vv{Y[2] * Y[3] + Y[1] + X[2], Y[1] * Y[3] + X[0] * X[2] + Y[3] + Y[1] + Y[0] + X[2] + X[1] + 1, Y[1] * Y[2] + X[0] * Y[3] + X[0] * X[2] + Y[3] + X[2], Y[0] * Y[3] + Y[3] + Y[2] + Y[0] + X[3], Y[0] * Y[2] + X[0] * Y[0] + Y[2] + Y[0] + X[0] + 1, Y[0] * Y[1] + X[0] * Y[2] + X[0] * Y[0] + X[0] * X[3] + Y[3] + Y[2] + Y[1] + Y[0] + X[2] + X[0] + 1, X[3] * Y[3] + Y[3] + Y[1] + X[2], X[3] * Y[2] + X[0] * Y[2] + X[0] * X[3] + Y[2] + X[3] + X[0] + 1, X[3] * Y[1] + Y[0] + X[3] + X[2] + X[1] + X[0], X[3] * Y[0] + X[0] * Y[0] + Y[2] + X[0] + 1, X[2] * Y[3] + X[0] * X[2] + Y[3] + Y[0] + X[1] + 1, X[2] * Y[2] + X[0] * Y[3] + X[0] * X[2] + Y[3] + Y[1], X[2] * Y[1] + X[0] * Y[0] + X[0] * X[1] + Y[1] + Y[0] + X[1] + X[0] + 1, X[2] * Y[0] + Y[3] + X[3] + X[0] + 1, X[2] * X[3] + Y[0] + X[3] + X[2] + X[1] + X[0], X[1] * Y[3] + X[0] * Y[3] + X[0] * Y[0] + X[0] * X[1] + Y[2] + X[3] + X[1] + X[0] + 1, X[1] * Y[2] + X[0] * Y[1] + X[0] * X[2] + X[0] * X[1] + X[1], X[1] * Y[1] + X[0] * Y[2] + X[0] * Y[1] + X[0] * X[3] + X[0] * X[1] + Y[3] + Y[2] + X[2] + X[1], X[1] * Y[0] + X[0] * X[3] + Y[2] + Y[1] + Y[0] + X[3] + X[2], X[1] * X[3] + X[0] * Y[0] + X[0] * X[3] + Y[2] + X[3] + X[0] + 1, X[1] * X[2] + X[0] * X[2] + Y[3] + X[3] + X[2] + X[0] + 1};
        return vv;
    }
    if (i == 5)
    {
        vector<BoolePolynomial> vv{Y[2] * Y[3] + Y[1] + X[2] + 1, Y[1] * Y[3] + X[0] * Y[2] + X[0] * X[2] + Y[3], Y[1] * Y[2] + X[0] * X[2] + Y[1] + Y[0] + X[1] + 1, Y[0] * Y[3] + X[0] * Y[0] + Y[3] + X[0], Y[0] * Y[2] + Y[3] + Y[2] + Y[0] + X[3], Y[0] * Y[1] + X[0] * Y[3] + X[0] * Y[0] + X[0] * X[3] + Y[2] + Y[1] + Y[0] + X[3] + X[2] + X[0] + 1, X[3] * Y[3] + X[0] * Y[3] + X[0] * X[3] + X[0], X[3] * Y[2] + Y[2] + Y[1] + X[2] + 1, X[3] * Y[1] + Y[0] + X[2] + X[1] + X[0], X[3] * Y[0] + X[0] * Y[0] + Y[3] + Y[0] + X[0], X[2] * Y[3] + X[0] * Y[2] + X[0] * X[2] + Y[1] + X[2] + 1, X[2] * Y[2] + X[0] * X[2] + Y[2] + Y[0] + X[2] + X[1], X[2] * Y[1] + X[0] * Y[0] + X[0] * X[1] + Y[1] + X[2] + 1, X[2] * Y[0] + Y[2] + X[3] + X[0], X[2] * X[3] + Y[0] + X[3] + X[2] + X[1] + X[0], X[1] * Y[3] + X[0] * Y[1] + X[0] * X[2] + X[0] * X[1] + Y[3] + Y[1] + X[2] + 1, X[1] * Y[2] + X[0] * Y[2] + X[0] * Y[0] + X[0] * X[1] + Y[3] + Y[0] + X[3], X[1] * Y[1] + X[0] * Y[3] + X[0] * Y[1] + X[0] * X[3] + X[0] * X[1] + Y[2] + X[3] + X[2] + X[1], X[1] * Y[0] + X[0] * X[3] + Y[3] + Y[1] + X[2] + 1, X[1] * X[3] + X[0] * Y[0] + X[0] * X[3] + Y[3] + Y[0] + X[3] + X[0], X[1] * X[2] + X[0] * X[2] + Y[2] + X[3] + X[2] + X[0]};
        return vv;
    }
    if (i == 6)
    {
        vector<BoolePolynomial> vv{Y[2] * Y[3] + X[0] * Y[0] + X[0] * X[2] + X[0], Y[1] * Y[3] + X[0] * Y[1] + Y[3] + X[0], Y[1] * Y[2] + X[0] * Y[3] + X[0] * Y[1] + X[0] * X[3] + Y[2] + Y[0] + X[3] + X[2] + X[0] + 1, Y[0] * Y[3] + Y[2] + X[2] + 1, Y[0] * Y[2] + X[0] * X[2] + Y[2] + Y[1] + Y[0] + X[1] + X[0], Y[0] * Y[1] + Y[3] + Y[1] + Y[0] + X[3], X[3] * Y[3] + X[0] * Y[3] + X[0] * X[3] + X[0], X[3] * Y[2] + Y[1] + X[3] + X[2] + X[1] + X[0] + 1, X[3] * Y[1] + X[0] * Y[1] + Y[3] + Y[1] + X[0], X[3] * Y[0] + Y[2] + Y[0] + X[2] + 1, X[2] * Y[3] + X[0] * Y[0] + X[0] * X[2] + Y[3] + Y[2] + X[2] + X[0] + 1, X[2] * Y[2] + X[0] * Y[1] + X[0] * X[1], X[2] * Y[1] + Y[1] + Y[0] + X[3] + X[0], X[2] * Y[0] + X[0] * X[2] + Y[1] + X[2] + X[1] + X[0] + 1, X[2] * X[3] + Y[1] + X[2] + X[1] + X[0] + 1, X[1] * Y[3] + X[0] * Y[2] + X[0] * X[2] + X[0] * X[1] + Y[3] + Y[2] + X[2] + 1, X[1] * Y[2] + X[0] * Y[3] + X[0] * Y[2] + X[0] * X[3] + X[0] * X[1] + Y[0] + X[3] + X[2] + X[0] + 1, X[1] * Y[1] + X[0] * X[3] + Y[3] + Y[2] + X[2] + 1, X[1] * Y[0] + X[0] * Y[1] + X[0] * Y[0] + X[0] * X[1] + Y[3] + Y[1] + X[3], X[1] * X[3] + X[0] * Y[1] + X[0] * X[3] + Y[3] + Y[1] + X[3] + X[0], X[1] * X[2] + X[0] * X[2] + Y[0] + X[3] + X[2] + X[1] + 1};
        return vv;
    }
    if (i == 7)
    {
        vector<BoolePolynomial> vv{Y[2] * Y[3] + X[0] * Y[0] + X[0] * X[2] + Y[0] + X[2], Y[1] * Y[3] + X[0] * Y[1] + Y[3] + Y[1] + X[0] + 1, Y[1] * Y[2] + X[0] * Y[3] + X[0] * Y[1] + X[0] * X[3] + Y[3] + Y[2] + Y[1] + Y[0] + X[2] + X[0] + 1, Y[0] * Y[3] + Y[2] + X[2], Y[0] * Y[2] + X[0] * X[2] + Y[2] + Y[1] + Y[0] + X[2] + X[1] + 1, Y[0] * Y[1] + Y[3] + Y[1] + Y[0] + X[3], X[3] * Y[3] + X[0] * Y[3] + X[0] * X[3] + Y[3] + X[3] + X[0] + 1, X[3] * Y[2] + Y[1] + X[3] + X[2] + X[1] + X[0], X[3] * Y[1] + X[0] * Y[1] + Y[3] + X[0] + 1, X[3] * Y[0] + Y[2] + Y[0] + X[2], X[2] * Y[3] + X[0] * Y[0] + X[0] * X[2] + Y[2] + Y[0], X[2] * Y[2] + X[0] * Y[1] + X[0] * X[1] + Y[2] + Y[1] + X[1] + X[0] + 1, X[2] * Y[1] + Y[0] + X[3] + X[0] + 1, X[2] * Y[0] + X[0] * X[2] + Y[1] + Y[0] + X[1] + 1, X[2] * X[3] + Y[1] + X[3] + X[2] + X[1] + X[0], X[1] * Y[3] + X[0] * Y[2] + X[0] * X[2] + X[0] * X[1] + X[1], X[1] * Y[2] + X[0] * Y[3] + X[0] * Y[2] + X[0] * X[3] + X[0] * X[1] + Y[3] + Y[0] + X[2] + X[1], X[1] * Y[1] + X[0] * X[3] + Y[3] + Y[2] + Y[1] + X[3] + X[2], X[1] * Y[0] + X[0] * Y[1] + X[0] * Y[0] + X[0] * X[1] + Y[3] + X[3] + X[1] + X[0] + 1, X[1] * X[3] + X[0] * Y[1] + X[0] * X[3] + Y[3] + X[3] + X[0] + 1, X[1] * X[2] + X[0] * X[2] + Y[0] + X[3] + X[2] + X[0] + 1};
        return vv;
    }
    if (i == 8)
    {
        vector<BoolePolynomial> vv{Y[2] * Y[3] + X[0] * Y[0] + X[0] * X[2] + Y[2], Y[1] * Y[3] + X[0] * Y[2] + X[0] * Y[1] + X[0] * X[3] + Y[3] + Y[1] + Y[0] + X[3] + X[2] + X[0] + 1, Y[1] * Y[2] + X[0] * Y[1] + Y[2] + X[0], Y[0] * Y[3] + X[0] * X[2] + Y[3] + Y[1] + X[1] + 1, Y[0] * Y[2] + Y[3] + X[2] + 1, Y[0] * Y[1] + Y[2] + Y[1] + Y[0] + X[3], X[3] * Y[3] + Y[1] + X[2] + X[1] + X[0], X[3] * Y[2] + X[0] * Y[2] + X[0] * X[3] + X[0], X[3] * Y[1] + X[0] * Y[1] + Y[2] + Y[1] + X[0], X[3] * Y[0] + Y[3] + Y[0] + X[2] + 1, X[2] * Y[3] + X[0] * Y[1] + X[0] * X[1] + Y[3] + X[2] + 1, X[2] * Y[2] + X[0] * Y[0] + X[0] * X[2] + Y[3] + X[2] + 1, X[2] * Y[1] + Y[0] + X[3] + X[0], X[2] * Y[0] + X[0] * X[2] + Y[1] + Y[0] + X[2] + X[1], X[2] * X[3] + Y[1] + X[3] + X[2] + X[1] + X[0], X[1] * Y[3] + X[0] * Y[3] + X[0] * Y[2] + X[0] * X[3] + X[0] * X[1] + Y[0] + X[3] + X[2] + X[1], X[1] * Y[2] + X[0] * Y[3] + X[0] * X[2] + X[0] * X[1] + Y[3] + Y[2] + X[2] + 1, X[1] * Y[1] + X[0] * X[3] + Y[3] + Y[2] + X[2] + 1, X[1] * Y[0] + X[0] * Y[1] + X[0] * Y[0] + X[0] * X[1] + Y[2] + Y[1] + X[3], X[1] * X[3] + X[0] * Y[1] + X[0] * X[3] + Y[2] + Y[1] + X[3] + X[0], X[1] * X[2] + X[0] * X[2] + Y[0] + X[3] + X[2] + X[0]};
        return vv;
    }
    if (i == 9)
    {
        vector<BoolePolynomial> vv{Y[2] * Y[3] + Y[3] + Y[2] + Y[0] + X[3], Y[1] * Y[3] + X[0] * X[2] + Y[3] + Y[2] + Y[1] + X[2] + X[1] + 1, Y[1] * Y[2] + X[0] * Y[2] + X[0] * Y[0] + X[0] * X[3] + Y[3] + Y[2] + Y[1] + Y[0] + X[2] + X[0] + 1, Y[0] * Y[3] + Y[1] + X[2], Y[0] * Y[2] + X[0] * Y[2] + Y[2] + Y[0] + X[0] + 1, Y[0] * Y[1] + X[0] * Y[3] + X[0] * X[2] + Y[3] + X[2], X[3] * Y[3] + Y[3] + Y[1] + X[2], X[3] * Y[2] + X[0] * Y[2] + Y[0] + X[0] + 1, X[3] * Y[1] + Y[2] + X[3] + X[2] + X[1] + X[0], X[3] * Y[0] + X[0] * Y[0] + X[0] * X[3] + Y[0] + X[3] + X[0] + 1, X[2] * Y[3] + X[0] * X[2] + Y[3] + Y[2] + X[1] + 1, X[2] * Y[2] + Y[3] + X[3] + X[0] + 1, X[2] * Y[1] + X[0] * Y[2] + X[0] * X[1] + Y[2] + Y[1] + X[1] + X[0] + 1, X[2] * Y[0] + X[0] * Y[3] + X[0] * X[2] + Y[3] + Y[1], X[2] * X[3] + Y[2] + X[3] + X[2] + X[1] + X[0], X[1] * Y[3] + X[0] * Y[3] + X[0] * Y[2] + X[0] * X[1] + Y[0] + X[3] + X[1] + X[0] + 1, X[1] * Y[2] + X[0] * X[3] + Y[2] + Y[1] + Y[0] + X[3] + X[2], X[1] * Y[1] + X[0] * Y[1] + X[0] * Y[0] + X[0] * X[3] + X[0] * X[1] + Y[3] + Y[0] + X[2] + X[1], X[1] * Y[0] + X[0] * Y[1] + X[0] * X[2] + X[0] * X[1] + X[1], X[1] * X[3] + X[0] * Y[2] + X[0] * X[3] + Y[0] + X[3] + X[0] + 1, X[1] * X[2] + X[0] * X[2] + Y[3] + X[3] + X[2] + X[0] + 1};
        return vv;
    }
    throw "Error In SBox";
}

vector<BoolePolynomial> SboxAdd(const vector<BoolePolynomial> &X, const vector<BoolePolynomial> &Y, const int i)
{
    //auto res=LbBoxAddMQ(X,Y,i);
    // auto res2=LbBoxAddFWBW(X,Y,i);
    // move(res2.begin(),res2.end(),inserter(res,res.end()));
    return LbBoxAddFWBW(X, Y, i);
}

vector<BoolePolynomial> LbPerm(const vector<BoolePolynomial> &X)
{
    vector<BoolePolynomial> T(32, ring);
    for (int i = 0; i < 4; i++)
    {
        T[7 * 4 + i] = X[6 * 4 + i];
        T[6 * 4 + i] = X[4 * 4 + i];
        T[5 * 4 + i] = X[7 * 4 + i];
        T[4 * 4 + i] = X[5 * 4 + i];
        T[3 * 4 + i] = X[2 * 4 + i];
        T[2 * 4 + i] = X[0 * 4 + i];
        T[1 * 4 + i] = X[3 * 4 + i];
        T[0 * 4 + i] = X[1 * 4 + i];
    }
    return T;
}

vector<BoolePolynomial> LbInvPerm(const vector<BoolePolynomial> &X)
{
    vector<BoolePolynomial> T(32, ring);
    for (int i = 0; i < 4; i++)
    {
        T[7 * 4 + i] = X[5 * 4 + i];
        T[6 * 4 + i] = X[7 * 4 + i];
        T[5 * 4 + i] = X[4 * 4 + i];
        T[4 * 4 + i] = X[6 * 4 + i];
        T[3 * 4 + i] = X[1 * 4 + i];
        T[2 * 4 + i] = X[3 * 4 + i];
        T[1 * 4 + i] = X[0 * 4 + i];
        T[0 * 4 + i] = X[2 * 4 + i];
    }
    return T;
}

void LbFMQ(vector<BoolePolynomial> &eqs, const vector<BoolePolynomial> &L, const vector<BoolePolynomial> &K, const vector<BoolePolynomial> &O)
{
    vector<BoolePolynomial> TT = LbInvPerm(O);
    vector<BoolePolynomial> T(32, ring);
    for (int i = 0; i < 32; i++)
        T[i] = L[i] + K[i];
    auto it_x = T.begin();
    auto it_y = TT.begin();
    for (int i = 0; i < 8; i++)
    {
        vector<BoolePolynomial> ee = SboxAdd(vector<BoolePolynomial>(it_x, it_x + 4), vector<BoolePolynomial>(it_y, it_y + 4), i);
        for (int j = 0; j < ee.size(); j++)
        {
            eqs.push_back(ee[j]);
            //cout<<ee[j]<<endl;
        }
        it_x += 4;
        it_y += 4;
    }
}

void LbKeyRoundEqsMQ(vector<BoolePolynomial> &keqs, int rnd, vector<BoolePolynomial> &Stt)
{
    vector<BoolePolynomial> T(80, ring);
    for (int i = 0; i < 80; i++)
        T[(i + 29) % 80] = Stt[i];
    auto it_T = T.begin();
    auto it_k = var_Keys.begin();

    vector<BoolePolynomial> ee = SboxAdd(vector<BoolePolynomial>(it_T + 76, it_T + 80), vector<BoolePolynomial>(it_k + 80 + rnd * 8 + 4, it_k + 80 + rnd * 8 + 8), 9);
    for (int i = 0; i < ee.size(); i++)
        keqs.push_back(ee[i]);

    ee = SboxAdd(vector<BoolePolynomial>(it_T + 72, it_T + 76), vector<BoolePolynomial>(it_k + 80 + rnd * 8 + 0, it_k + 80 + rnd * 8 + 4), 8);
    for (int i = 0; i < ee.size(); i++)
        keqs.push_back(ee[i]);
    for (int i = 0; i < 8; i++)
        T[72 + i] = var_Keys[80 + rnd * 8 + i];
    for (int i = 0; i < 5; i++)
        T[46 + i] += (((rnd + 1) >> i) & 0x1);
    Stt = T;
}

vector<BoolePolynomial> RotL8(const vector<BoolePolynomial> &X)
{
    vector<BoolePolynomial> RR(32, ring);
    for (int i = 0; i < 32; i++)
        RR[i] = X[(i + 24) % 32];
    return RR;
}

void AIOEncryptEqs(vector<BoolePolynomial> &eqs,
                   const vector<BoolePolynomial> &forward_eqs,
                   const bitset<IGNORE_BITSET_SIZE> &ignore_set,
                   const vector<BoolePolynomial> &K,
                   const vector<vector<BoolePolynomial>> &X,
                   const vector<vector<BoolePolynomial>> &Y)
{
    vector<BoolePolynomial> Stt = K;
    //list<BoolePolynomial> keqs;
    vector<vector<vector<BoolePolynomial>>> L(Nm, vector<vector<BoolePolynomial>>(Nr + 3, vector<BoolePolynomial>(32, ring)));
    for (int i = 0; i < Nm; i++)
    {
        for (int j = 0; j < 32; j++)
        {
            L[i][0][j] = X[i][j];
            L[i][1][j] = X[i][32 + j];
            L[i][Nr][j] = Y[i][32 + j];
            L[i][Nr + 1][j] = Y[i][j];
        }
        for (int j = 1; j < Nr - 1; j++)
        {
            for (int k = 0; k < 32; k++)
            {
                L[i][j + 1][k] = var_L[i][j][k];
            }
        }
    }

    for (auto it = forward_eqs.begin(); it != forward_eqs.end(); it++)
    {
        if (it->deg() == 1)
        {
            BooleMonomial mon = it->lead();
            auto v = *(mon.begin());
            if (ring.getVariableName(v)[0] == 'L')
            {
                int i, j, k;
                sscanf(ring.getVariableName(v), "L_%d_%d_%d", &i, &j, &k);
                L[i][j + 1][k] += *it;
                //cout<<L[i][j+1][k]<<","<<*it<<endl;
            }
        }
    }

    for (int i = 0; i < Nr; i++)
    {

        vector<BoolePolynomial> rk(32, ring);
        for (int k = 0; k < 32; k++)
            rk[k] = Stt[48 + k];
        groebner::ReductionStrategy generators(ring);
        generators.optRedTailDegGrowth = true;
        generators.optRedTail = true;

        for (int j = Nm - 1; j >= 0; j--)
        {
            vector<BoolePolynomial> reqs;
            vector<BoolePolynomial> t = RotL8(L[j][i]);
            for (int k = 0; k < 32; k++)
            {
                t[k] += L[j][i + 2][k];
                //cout<<t[k]<<endl;
            }
            LbFMQ(reqs, L[j][i + 1], rk, t);
            for (auto it = reqs.begin(); it != reqs.end(); it++)
            {
                auto p = generators.nf(*it);
                if (!p.isZero())
                {
                    generators.addGenerator(p);
                    eqs.push_back(*it);
                }
            }
        }

        if (i < Nr - 1)
            LbKeyRoundEqsMQ(eqs, i, Stt);
    }
}

vector<BoolePolynomial>
MonomialAnalysis(
    const vector<BoolePolynomial> eqs[Nr],
    bool forward,
    const vector<__uint64_t> &ZZ_N,
    set<BooleMonomial> &excluded_mon,
    const int prot = 0)
{
    vector<int> idxs;
    for (int i = 0; i < Nm; i++)
        idxs.push_back(i);
    set<BooleMonomial> set_monos;
    vector<BooleMonomial> monos;
    vector<BoolePolynomial> res;
    for (int i = 0; i < Nr; i++)
    {
        set_monos.clear();
        list<BoolePolynomial> teqs;
        for (auto it_p = eqs[i].begin(); it_p != eqs[i].end(); it_p++)
        {
            for (auto it_m = it_p->begin(); it_m != it_p->end(); it_m++)
            {
                BooleMonomial mon = *it_m;
                if (any_of(mon.variableBegin(), mon.variableEnd(), [](const BooleVariable &v) { return (ring.getVariableName(v.index())[0] == 'K'); }))
                    continue;
                if (excluded_mon.find(mon) == excluded_mon.end())
                    set_monos.insert(mon);
            }
        }
        move(set_monos.begin(), set_monos.end(), inserter(monos, monos.end()));
        sort(monos.begin(), monos.end());
        reverse(monos.begin(), monos.end());
        monos.push_back(BooleMonomial(ring));
        DoElimination(teqs, forward, idxs, monos, ZZ_N, prot);
        move(teqs.begin(), teqs.end(), inserter(res, res.end()));
        for (auto it = teqs.begin(); it != teqs.end(); it++)
        {
            auto mon = (*it).lead();
            excluded_mon.insert(mon);
        }
        if (prot)
        {
            cout << "-------------" << endl;
            cout << "Rnd: " << i << " ,#idxs: " << idxs.size() << ", #teqs: " << teqs.size() << endl;
            cout << "-------------" << endl;
        }
    }
    //res=ElimLin(res);

    set_monos.clear();
    for (int i = 0; i < Nr; i++)
    {
        for (auto it_p = eqs[i].begin(); it_p != eqs[i].end(); it_p++)
        {
            for (auto it_m = it_p->begin(); it_m != it_p->end(); it_m++)
            {
                BooleMonomial mon = *it_m;
                if (any_of(mon.variableBegin(), mon.variableEnd(), [](const BooleVariable &v) { return (ring.getVariableName(v.index())[0] == 'K'); }))
                    continue;
                if (excluded_mon.find(mon) == excluded_mon.end())
                    set_monos.insert(mon);
            }
        }
    }
    if (1)
    {
        list<BoolePolynomial> teqs;
        move(set_monos.begin(), set_monos.end(), inserter(monos, monos.end()));
        sort(monos.begin(), monos.end());
        reverse(monos.begin(), monos.end());
        monos.push_back(BooleMonomial(ring));
        DoElimination(teqs, forward, idxs, monos, ZZ_N, prot);
        move(teqs.begin(), teqs.end(), inserter(res, res.end()));
        for (auto it = teqs.begin(); it != teqs.end(); it++)
        {
            auto mon = (*it).lead();
            excluded_mon.insert(mon);
        }
        if (prot)
        {
            cout << "-------------" << endl;
            cout << "Rnd: "
                 << "All"
                 << " ,#idxs: " << idxs.size() << ", #teqs: " << teqs.size() << endl;
            cout << "-------------" << endl;
        }
    }
    if (prot)
        cout << "#eqs: " << res.size() << endl;
    return res;
}

vector<BoolePolynomial>
MonomialAnalysisProne(
    const vector<BoolePolynomial> eqs[Nr],
    const vector<__uint64_t> &ZZ_X,
    const vector<__uint64_t> &ZZ_Y,
    set<BooleMonomial> &excluded_mon,
    const int prot = 0)
{
    vector<int> idxs;
    for (int i = 0; i < Nm; i++)
        idxs.push_back(i);
    set<BooleMonomial> set_monos;
    vector<BooleMonomial> monos;
    vector<BoolePolynomial> res;
    for (int i = 0; i < Nr; i++)
    {
        set_monos.clear();
        list<BoolePolynomial> teqs;
        for (auto it_p = eqs[i].begin(); it_p != eqs[i].end(); it_p++)
        {
            for (auto it_m = it_p->begin(); it_m != it_p->end(); it_m++)
            {
                BooleMonomial mon = *it_m;
                if (any_of(mon.variableBegin(), mon.variableEnd(), [](const BooleVariable &v) { return (ring.getVariableName(v.index())[0] == 'K'); }))
                    continue;
                if (excluded_mon.find(mon) == excluded_mon.end())
                    set_monos.insert(mon);
            }
        }
        move(set_monos.begin(), set_monos.end(), inserter(monos, monos.end()));
        sort(monos.begin(), monos.end());
        reverse(monos.begin(), monos.end());
        monos.push_back(BooleMonomial(ring));
        DoEliminationProne(teqs, idxs, monos, ZZ_X, ZZ_Y, prot);
        move(teqs.begin(), teqs.end(), inserter(res, res.end()));
        for (auto it = teqs.begin(); it != teqs.end(); it++)
        {
            auto mon = (*it).lead();
            excluded_mon.insert(mon);
        }
        if (prot)
        {
            cout << "-------------" << endl;
            cout << "Rnd: " << i << " ,#idxs: " << idxs.size() << ", #teqs: " << teqs.size() << endl;
            cout << "-------------" << endl;
        }
    }
    //res=ElimLin(res);

    set_monos.clear();
    for (int i = 0; i < Nr; i++)
    {
        for (auto it_p = eqs[i].begin(); it_p != eqs[i].end(); it_p++)
        {
            for (auto it_m = it_p->begin(); it_m != it_p->end(); it_m++)
            {
                BooleMonomial mon = *it_m;
                if (any_of(mon.variableBegin(), mon.variableEnd(), [](const BooleVariable &v) { return (ring.getVariableName(v.index())[0] == 'K'); }))
                    continue;
                if (excluded_mon.find(mon) == excluded_mon.end())
                    set_monos.insert(mon);
            }
        }
    }
    if (1)
    {
        list<BoolePolynomial> teqs;
        move(set_monos.begin(), set_monos.end(), inserter(monos, monos.end()));
        sort(monos.begin(), monos.end());
        reverse(monos.begin(), monos.end());
        monos.push_back(BooleMonomial(ring));
        DoEliminationProne(teqs, idxs, monos, ZZ_X, ZZ_Y, prot);
        move(teqs.begin(), teqs.end(), inserter(res, res.end()));
        for (auto it = teqs.begin(); it != teqs.end(); it++)
        {
            auto mon = (*it).lead();
            excluded_mon.insert(mon);
        }
        if (prot)
        {
            cout << "-------------" << endl;
            cout << "Rnd: "
                 << "All"
                 << " ,#idxs: " << idxs.size() << ", #teqs: " << teqs.size() << endl;
            cout << "-------------" << endl;
        }
    }
    if (prot)
        cout << "#eqs: " << res.size() << endl;
    return res;
}
