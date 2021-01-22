
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
#include <sys/wait.h>

#define SBOX_SIZE                   4
#define NUMBER_OF_SBOX_IN_ROUND     (INT_BIT_SIZE/SBOX_SIZE)
#define IGNORE_BITSET_SIZE          (Nm*Nr*NUMBER_OF_SBOX_IN_ROUND*NUM_SBOX_EQS)
#define ToIgnoreSboxIndex(k,i,j,l)  ((k)*(Nr*NUMBER_OF_SBOX_IN_ROUND*NUM_SBOX_EQS) + (i)*(NUMBER_OF_SBOX_IN_ROUND*NUM_SBOX_EQS)+ \
                                        (j)*(NUM_SBOX_EQS)+(l))

#define CHOSEN_PLAINTEXT    0
#define CHOSEN_CIPHERTEXT   1
#define KNOWN_PLAINTEXT     2
#define KNOWN_CIPHERTEXT    3
#define VARIABLE_ELIMLEN_LIMIT  (Nm)

#define WRONG_KEY_GUESS     0
#define RIGHT_KEY_GUESS     1

#define EXECIVE_SAMPLES     (256)

#define IS_CHOSEN_SCENARIO(s) (((s)==CHOSEN_PLAINTEXT) || ((s) == CHOSEN_CIPHERTEXT))
#define IS_PLAINTEXT_BASED(s) (((s)==CHOSEN_PLAINTEXT) || ((s) == KNOWN_PLAINTEXT))

void* SetKey(int nr, bitset<KeySchedSize>& key);
__uint64_t encryptTap(int type,__uint64_t ptext,const void* ctx,INT_TYPE tap[][2]);
__uint64_t decryptTap(int type,__uint64_t ctext, const void* ctx,INT_TYPE tap[][2]);
vector<BoolePolynomial> SboxAdd(const vector<BoolePolynomial>& X, const vector<BoolePolynomial>& Y,int index=0);
void AIOEncryptEqs(vector<BoolePolynomial>& eqs,
                       const vector<BoolePolynomial>& forward_eqs,
                       const bitset<IGNORE_BITSET_SIZE>& ignore_set,
                       const vector<BoolePolynomial>& K,
                       const vector< vector<BoolePolynomial> >& X,
                       const vector< vector<BoolePolynomial> >& Y);

random_device rd;

BoolePolyRing ring_sbox(2*SBOX_SIZE,CTypes::dp_asc);


unsigned int Rd32() {
	return rd();
}
__uint64_t Rd64() {
	__uint64_t T = 0;
	T = rd();
	T <<= 32;
	T ^= rd();
	return T;
}


class BitVector {
private:
	INT_TYPE reg;
public:
	BitVector(INT_TYPE val = 0) {
		reg = val;
	}

	BitVector operator^(const BitVector& b) const {
		return BitVector(reg ^ b.reg);
	}
	void operator^=(const BitVector& b) {
			reg ^= b.reg;
		}

	BitVector operator&(const BitVector& b) const {
			return BitVector(reg & b.reg);
		}

	void operator&=(const BitVector& b) {
				reg &= b.reg;
			}

    BitVector operator>>(const int& n) {
            BitVector a(*this);
            a.reg>>=n;
            return a;
    }

	INT_TYPE operator[](int idx) const {
		if (idx < INT_BIT_SIZE)
			return ((reg >> idx) & 1);
		throw "Error";
	}
	BitVector(const BitVector& a) {
		reg = a.reg;
	}
	bool operator==(unsigned int n) const {
		return (reg == n);
	}
	;
	bool operator==(const BitVector& b) const {
		return (reg == b.reg);
	}
	;
	bool operator!=(const BitVector& b) const {
		return (reg != b.reg);
	}
	;
	bool operator!=(const __uint32_t& b) const {
		return (reg != b);
	};
	INT_TYPE intVal()
	{
		return reg;
	}

};

typedef struct __T_NmNr{

	bitset<KeySchedSize> key;
	vector< vector<BitVector> > d[2];
	vector<uint64_t> x;
	vector<uint64_t> y;
	const int Nm;
	const int Nr;
	__T_NmNr(const int nm, const int nr):Nm(nm),Nr(nr)
	{
		d[0].resize(Nm);
        d[1].resize(Nm);
		for(int i=0;i<Nm;i++)
        {
			d[0][i].resize(Nr);
            d[1][i].resize(Nr);
        }
		x.resize(Nm);
		y.resize(Nm);

	};
	__T_NmNr( const  __T_NmNr& obj):Nm(obj.Nm),Nr(obj.Nr)
	{
		key = obj.key;
		for(int i=0;i<Nm;i++)
		{
			x[i] = obj.x[i];
			y[i] = obj.y[i];
			for(int j=0;j<Nr;j++)
            {
				d[0][i][j] = obj.d[0][i][j];
                d[1][i][j] = obj.d[1][i][j];
            }
        }


	};
} T_NmNr;


typedef vector<tuple<char,int,int,int,CAuxTypes::idx_type> >  IndexMonomial;


__uint64_t num_to_patt(int n, const vector<int>& patt) {
	__uint64_t x = 0;

	for (unsigned int  i = 0; i < patt.size(); i++)
		x |= ((n >> i) & 1) * (((__uint64_t ) 0x1) << patt[i]);
	return x;
}

__uint64_t num_to_textpatt(int n, const vector<int>& patt) {
	__uint64_t x = 0;//0x1<<n;
	for (unsigned int i = 0; i < patt.size(); i++)
		x |= ((n >> i) & 1) * (((__uint64_t ) 0x1) << patt[i]);
	return x;
}



IndexMonomial mono_to_idxmono(const vector<int>& map,const BooleMonomial& mon)
{

	IndexMonomial idxmon;
	int i,j,k;
	for(auto it= mon.variableBegin();it!=mon.variableEnd();it++)
	{
		CAuxTypes::idx_type idx = (*it).index();
		const char* str=ring.getVariableName(idx);
		switch(str[0])
		{
			case '1':
				idxmon.push_back(make_tuple('1',0,0,0,idx));
					break;
				case 'L':
					sscanf(str,"L_%d_%d_%d",&i,&j,&k);
					idxmon.push_back(make_tuple('L',map[i],	j,k,idx));
					break;
				case 'K':
					sscanf(str,"K%d",&i);
					idxmon.push_back(make_tuple('K',i,0,0,idx));
					break;
				case 'X':
					sscanf(str,"X_%d_%d",&i,&j);
					idxmon.push_back(make_tuple('X',map[i],j,0,idx));
					break;
				case 'Y':
					sscanf(str,"Y_%d_%d",&i,&j);
					idxmon.push_back(make_tuple('Y',map[i],j,0,idx));
					break;
				default:
					throw "Bad Monomial";

		}
				//cout<<idx_m<<","<<idx_i<<","<<idx_j<<endl;
	}

	return idxmon;
}

uint32_t apply_monomial( const IndexMonomial& mono, const T_NmNr& smp) {
	uint32_t And=1;
		for (auto it_a = mono.begin(); it_a != mono.end(); it_a++)
		{
			switch(get<0>(*it_a))
			{
			case 'L':
				And &= smp.d[0][get<1>(*it_a)][get<2>(*it_a)][get<3>(*it_a)];
				break;
			case 'K':
				And &= (smp.key[get<1>(*it_a)]) ? 0x1 : 0x0;
				break;
			case 'X':
				And &= (smp.x[get<1>(*it_a)]>>(get<2>(*it_a)));
				break;
			case 'Y':
				And &= (smp.y[get<1>(*it_a)]>>(get<2>(*it_a)));
				break;
			case '1':
				And &= (INT_TYPE) 1;
				break;
			default:
				throw "Bad Monomial";
			}

		}
	return (And);
}

uint32_t apply_polynomial( const vector<IndexMonomial>& poly, const T_NmNr& smp) {
	uint32_t Sum=0;
    for (auto it = poly.begin(); it != poly.end(); it++)
	{
        Sum ^= apply_monomial(*it,smp);
	}
	return (Sum);
}
BooleMonomial idxmono_to_mono(const vector<int>& map,const IndexMonomial& idxmono) {
	BooleMonomial mon(ring);
	for (auto it_a = idxmono.begin(); it_a != idxmono.end(); it_a++)
	{
		mon *= ring.variable(get<4>(*it_a));

	}
	return mon;
}

bitset<KeySize> GuessedKey;

vector<BoolePolynomial> GenerateSampleMatrix(
        bool forward,
		const int Nsmpls,
		const vector<int>& lst_idx,
		const vector<BooleMonomial>& lst_monos,
		const vector<__uint64_t> ZZ,
        const int prot=0) {
	timespec start, finish;
	double elp;
	int cNm = lst_idx.size();
	vector<int> map_idx_to_mon;
	vector<int> map_mon_to_idx;
	vector<IndexMonomial> lst_idxmons;

	map_idx_to_mon.resize(lst_idx.size());
	for (unsigned int i = 0; i < map_idx_to_mon.size(); i++){
			map_idx_to_mon[i] = lst_idx[i];
	}

	int max_num = *std::max_element(map_idx_to_mon.begin(),map_idx_to_mon.end())+1;
	map_mon_to_idx.resize(max_num);
	for(unsigned int i=0;i<map_mon_to_idx.size();i++)
		map_mon_to_idx[i]=-1;

	for (unsigned int i = 0; i < map_idx_to_mon.size(); i++){
			map_mon_to_idx[map_idx_to_mon[i]] = i;
		}



	lst_idxmons.resize(lst_monos.size());
	for(unsigned int i=0;i<lst_monos.size();i++)
		lst_idxmons[i] = mono_to_idxmono(map_mon_to_idx,lst_monos[i]);

	int dim_sample = lst_monos.size();
	int Nsamples = ((Nsmpls+127)/128)*128;

	mzd_t *mat = mzd_init(dim_sample, dim_sample + Nsamples);
	if(mat == NULL)
		throw "Cannot allocate matrix.";

	for (int i = 0; i < dim_sample; i++)
		for (int j = 0; j < dim_sample + Nsamples; j++)
			mzd_write_bit(mat, i, j, 0);

	if(prot)
		cout << dim_sample<<","<<dim_sample + Nsamples<<endl;

	clock_gettime(CLOCK_MONOTONIC,&start);
#pragma omp parallel for
	for (int iii = 0; iii < (Nsamples/64); iii++) {
        bitset<KeySchedSize> prv_keys[2];
		for(int ii=0;ii<64;ii++)
		{	int i=iii*64+ii;
			T_NmNr smp(cNm,Nr);
            if(CONSIDER_KEY_VARS && CUBE_LIKE_SAMPLES)
            {
                if(ii%3<2)
                {
                    for (int j = 0; j < KeySize; j++) {
                        smp.key[j] = Rd32() & 0x1;
                    }
                    prv_keys[ii%3] = smp.key;
                }
                else
                {
                    smp.key = prv_keys[0]^prv_keys[1];
                }
            }
            else
            {
                for (int j = 0; j < KeySize; j++) {
                    smp.key[j] = Rd32() & 0x1;
                }
            }
            for(int k=0;k<GUESS_BITS;k++)
                smp.key[k] = GuessedKey[k];
			void* ctx = SetKey(Nr, smp.key);
			for (int jj = 0; jj < cNm; jj++) {
				INT_TYPE tmpVals[Nr][2];
				if(forward)
				{
					smp.x[jj]=ToStateXY(ZZ[jj]);
					smp.y[jj]=ToStateXY(encryptTap(0, ZZ[jj], ctx, tmpVals));
				}
				else
				{
					smp.y[jj]=ToStateXY(ZZ[jj]);
					smp.x[jj]=ToStateXY(decryptTap(0, ZZ[jj], ctx, tmpVals));

				}
				for (int k = 0; k < Nr; k++)
					smp.d[0][jj][k] = ToStateI(tmpVals[k][0]);
			}

			for(int j=0;j<dim_sample;j++)
			{
				int v=apply_monomial(lst_idxmons[j],smp)&0x1;
				mzd_write_bit(mat,j,i,v);
			}

			free(ctx);
		}
	}


	clock_gettime(CLOCK_MONOTONIC,&finish);
	elp = (finish.tv_sec - start.tv_sec);
	elp += (finish.tv_nsec - start.tv_nsec) / 1000000000.0;
	if(prot)
		cout<<"Sample time:"<<elp<<endl;

	for (int i = 0; i < dim_sample; i++)
		mzd_write_bit(mat, i, Nsamples + i, 1);
	if(prot)
		cout << "Samples Collected" << endl;

	clock_gettime(CLOCK_MONOTONIC,&start);
	mzd_echelonize(mat, 1);
	//ParalleEchelonize(mat);
	//FullEchelonize(mat);
	mzd_t* wnd = mzd_init_window(mat,0,0,dim_sample,Nsamples);
	int rank=mzd_first_zero_row(wnd);
	mzd_free_window(wnd);
	clock_gettime(CLOCK_MONOTONIC,&finish);
	elp = (finish.tv_sec - start.tv_sec);
	elp += (finish.tv_nsec - start.tv_nsec) / 1000000000.0;
	if(prot){
	cout<<"RREF time:"<<elp<<endl;
	cout<<"Rank:"<<rank<<endl;
	}

	vector<BoolePolynomial> res;

	for(int i=rank;i<dim_sample;i++){
			BoolePolynomial poly(ring);
			for(int j=Nsamples;j<Nsamples+dim_sample;j++)
            {
				if(mzd_read_bit(mat,i,j))
				{
					poly+=idxmono_to_mono(map_idx_to_mon,lst_idxmons[j-Nsamples]);
				}
            }
				//cout<<poly<<endl;
				if(! poly.isZero())
					res.push_back(poly);
				//else
				//	cout<<"aLL zERO:"<<idxmono_to_mono(map_idx_to_mon,lst_idxmons[i])<<endl;

		}
	mzd_free(mat);
	return res;
}


vector<BoolePolynomial> GenerateSampleMatrixProne(
		const int Nsmpls,
		const vector<int>& lst_idx,
		const vector<BooleMonomial>& lst_monos,
		const vector<__uint64_t> ZZ_X,
        const vector<__uint64_t> ZZ_Y,
		const int prot=0) {
	timespec start, finish;
	double elp;
	int cNm = lst_idx.size();
	vector<int> map_idx_to_mon;
	vector<int> map_mon_to_idx;
	vector<IndexMonomial> lst_idxmons;

	map_idx_to_mon.resize(lst_idx.size());
	for (unsigned int i = 0; i < map_idx_to_mon.size(); i++){
			map_idx_to_mon[i] = lst_idx[i];
	}

	int max_num = *std::max_element(map_idx_to_mon.begin(),map_idx_to_mon.end())+1;
	map_mon_to_idx.resize(max_num);
	for(unsigned int i=0;i<map_mon_to_idx.size();i++)
		map_mon_to_idx[i]=-1;

	for (unsigned int i = 0; i < map_idx_to_mon.size(); i++){
			map_mon_to_idx[map_idx_to_mon[i]] = i;
		}


	lst_idxmons.resize(lst_monos.size());
	for(unsigned int i=0;i<lst_monos.size();i++)
		lst_idxmons[i] = mono_to_idxmono(map_mon_to_idx,lst_monos[i]);

	int dim_sample = 2*lst_monos.size();
	int Nsamples = ((2*Nsmpls+127)/128)*128;

	mzd_t *mat = mzd_init(dim_sample, dim_sample + Nsamples);
	if(mat == NULL)
		throw "Cannot allocate matrix.";

	for (int i = 0; i < dim_sample; i++)
		for (int j = 0; j < dim_sample + Nsamples; j++)
			mzd_write_bit(mat, i, j, 0);

	if(prot)
		cout << dim_sample<<","<<dim_sample + Nsamples<<endl;

	clock_gettime(CLOCK_MONOTONIC,&start);
#pragma omp parallel for
	for (int iii = 0; iii < (Nsamples/64); iii++) {
        bitset<KeySchedSize> prv_keys[2];
		for(int ii=0;ii<64;ii++)
		{
            int i=iii*64+ii;
			T_NmNr smp(cNm,Nr);
			if(CONSIDER_KEY_VARS && CUBE_LIKE_SAMPLES)
            {
                if(ii%3<2)
                {
                    for (int j = 0; j < KeySize; j++) {
                        smp.key[j] = Rd32() & 0x1;
                    }
                    prv_keys[ii%3] = smp.key;
                }
                else
                {
                    smp.key = prv_keys[0]^prv_keys[1];
                }
            }
            else
            {
                for (int j = 0; j < KeySize; j++) {
                    smp.key[j] = Rd32() & 0x1;
                }
            }
            for(int k=0;k<GUESS_BITS;k++)
                smp.key[k] = GuessedKey[k];

			void* ctx = SetKey(Nr, smp.key);
			for (int jj = 0; jj < cNm; jj++) {
				INT_TYPE tmpVals[Nr][2];
					smp.x[jj]=ToStateXY(ZZ_X[jj]);
					smp.y[jj]=ToStateXY(encryptTap(0, ZZ_X[jj], ctx, tmpVals));

				for (int k = 0; k < Nr; k++)
					smp.d[0][jj][k] = ToStateI(tmpVals[k][0]);
			}

			for(int j=0;j<dim_sample/2;j++)
			{
				int v=apply_monomial(lst_idxmons[j],smp)&0x1;
				mzd_write_bit(mat,j,i,v);
			}

			for (int jj = 0; jj < cNm; jj++) {
				INT_TYPE tmpVals[Nr][2];
					smp.y[jj]=ToStateXY(ZZ_Y[jj]);
					smp.x[jj]=ToStateXY(decryptTap(0, ZZ_Y[jj], ctx, tmpVals));

				for (int k = 0; k < Nr; k++)
					smp.d[0][jj][k] = ToStateI(tmpVals[k][0]);
			}

			for(int j=dim_sample/2;j<dim_sample;j++)
			{
				int v=apply_monomial(lst_idxmons[j-dim_sample/2],smp)&0x1;
				mzd_write_bit(mat,j,i,v);
			}


			free(ctx);
		}
	}


	clock_gettime(CLOCK_MONOTONIC,&finish);
	elp = (finish.tv_sec - start.tv_sec);
	elp += (finish.tv_nsec - start.tv_nsec) / 1000000000.0;
	if(prot)
		cout<<"Sample time:"<<elp<<endl;

	for (int i = 0; i < dim_sample; i++)
		mzd_write_bit(mat, i, Nsamples + i, 1);
	if(prot)
		cout << "Samples Collected" << endl;

	clock_gettime(CLOCK_MONOTONIC,&start);
	mzd_echelonize(mat, 1);
	mzd_t* wnd = mzd_init_window(mat,0,0,dim_sample,Nsamples);
	int rank=mzd_first_zero_row(wnd);
	mzd_free_window(wnd);
	clock_gettime(CLOCK_MONOTONIC,&finish);
	elp = (finish.tv_sec - start.tv_sec);
	elp += (finish.tv_nsec - start.tv_nsec) / 1000000000.0;
	if(prot){
	cout<<"RREF time:"<<elp<<endl;
	cout<<"Rank:"<<rank<<endl;
	}

	vector<BoolePolynomial> res;

	for(int i=rank;i<dim_sample;i++){
			BoolePolynomial poly(ring);
			for(int j=Nsamples;j<Nsamples+dim_sample/2;j++)
            {
				if(mzd_read_bit(mat,i,j))
				{
					poly+=idxmono_to_mono(map_idx_to_mon,lst_idxmons[j-Nsamples]);
				}
            }
            for(int j=Nsamples+dim_sample/2;j<Nsamples+dim_sample;j++)
            {
				if(mzd_read_bit(mat,i,j))
				{
					poly+=idxmono_to_mono(map_idx_to_mon,lst_idxmons[j-Nsamples-dim_sample/2]);
				}
            }

            //cout<<poly<<endl;
            if(! poly.isZero())
                res.push_back(poly);
            //else
            //	cout<<"aLL zERO:"<<idxmono_to_mono(map_idx_to_mon,lst_idxmons[i])<<endl;

    }
	mzd_free(mat);
	return res;
}


uint32_t apply_sbox_monomial( const vector<int>& mono, const BitVector& X,const BitVector& Y) {
	uint32_t And=1;
    if(mono.size()==0)
        return 0;
    for (auto it_a = mono.begin(); it_a != mono.end(); it_a++)
	{
        int v = *it_a;
        if(v<SBOX_SIZE)
            And &= X[v];
        else if(v<2*SBOX_SIZE)
            And &= Y[v-SBOX_SIZE];
		else
            throw "Bad Sbox Monomial";
	}
	return (And);
}

vector<array<int,4> > GenerateSampleSuperMatrix(
        bool forward,
		const int Nsmpls,
        const vector<array<int,4> >& sboxes,
		const vector<BoolePolynomial>& lst_sbox_polys,
		const vector<__uint64_t> ZZ,
        const int prot=0) {
	timespec start, finish;
	double elp;

	const int dim_sample = sboxes.size();
    set<BooleMonomial> set_monos;
    vector<BooleMonomial> monos;
    vector<vector<vector<int> > >  idx_monos;
    for(auto it=lst_sbox_polys.begin();it!=lst_sbox_polys.end();it++)
    {
        for(auto it_m=it->begin();it_m!=it->end();it_m++)
        {
            set_monos.insert(*it_m);
        }

    }
    move(set_monos.begin(),set_monos.end(),inserter(monos,monos.end()));
    const int block_size = monos.size();
    idx_monos.resize(lst_sbox_polys.size());
    for(unsigned int i=0;i<lst_sbox_polys.size();i++)
    {
        idx_monos[i].resize(block_size);
        for(int j=0;j<block_size;j++)
        {
            if(find(lst_sbox_polys[i].begin(),lst_sbox_polys[i].end(),monos[j])!=lst_sbox_polys[i].end())
            {
                BooleMonomial m = monos[j];
                for(auto it_v = m.variableBegin();it_v!= m.variableEnd();it_v++)
                {
                    int pos;
                    CAuxTypes::idx_type idx = it_v->index();
                    const char* str_v=ring_sbox.getVariableName(idx);
                    sscanf(&str_v[1],"%d",&pos);
                    if(pos<0 || pos > SBOX_SIZE)
                        throw "Bad Sbox Monomial.";
                    if(str_v[0] == 'X')
                        idx_monos[i][j].push_back(pos);
                    else if(str_v[0] == 'Y')
                        idx_monos[i][j].push_back(pos+SBOX_SIZE);
                    else
                        throw "Bad Sbox Monomial.";
                }

            }
        }
    }

	int Nsamples = (((Nsmpls/block_size+127)/128)*128);

	mzd_t *mat = mzd_init(dim_sample, dim_sample + Nsamples*block_size);
	if(mat == NULL)
		throw "Cannot allocate matrix.";

	for (int i = 0; i < dim_sample; i++)
		for (int j = 0; j < dim_sample + Nsamples; j++)
			mzd_write_bit(mat, i, j, 0);

	if(prot)
		cout << dim_sample<<","<<dim_sample + Nsamples*block_size<<endl;

	clock_gettime(CLOCK_MONOTONIC,&start);
#pragma omp parallel for
	for (int iii = 0; iii < (Nsamples/64); iii++) {
        bitset<KeySchedSize> prv_keys[2];
		for(int ii=0;ii<64;ii++)
		{	int i=iii*64+ii;
			T_NmNr smp(Nm,Nr);
            if(CONSIDER_KEY_VARS && CUBE_LIKE_SAMPLES)
            {
                if(ii%3<2)
                {
                    for (int j = 0; j < KeySize; j++) {
                        smp.key[j] = Rd32() & 0x1;
                    }
                    prv_keys[ii%3] = smp.key;
                }
                else
                {
                    smp.key = prv_keys[0]^prv_keys[1];
                }
            }
            else
            {
                for (int j = 0; j < KeySize; j++) {
                    smp.key[j] = Rd32() & 0x1;
                }
            }
            for(int k=0;k<GUESS_BITS;k++)
                smp.key[k] = GuessedKey[k];
			void* ctx = SetKey(Nr, smp.key);
			for (int jj = 0; jj < Nm; jj++) {
				INT_TYPE tmpVals[Nr][2];
				if(forward)
				{
					smp.x[jj]=ToStateXY(ZZ[jj]);
					smp.y[jj]=ToStateXY(encryptTap(1, ZZ[jj], ctx, tmpVals));
				}
				else
				{
					smp.y[jj]=ToStateXY(ZZ[jj]);
					smp.x[jj]=ToStateXY(decryptTap(1, ZZ[jj], ctx, tmpVals));

				}
				for (int k = 0; k < Nr; k++)
                {
					smp.d[0][jj][k] = ToStateI(tmpVals[k][0]);
                    smp.d[1][jj][k] = ToStateI(tmpVals[k][1]);
                }
			}

			for(unsigned int j=0;j<sboxes.size();j++)
			{
                BitVector x=smp.d[0][sboxes[j][0]][sboxes[j][1]]>>(sboxes[j][2]*SBOX_SIZE);
                BitVector y=smp.d[1][sboxes[j][0]][sboxes[j][1]]>>(sboxes[j][2]*SBOX_SIZE);
                for(int k=0;k<block_size;k++)
                {
                    int v=apply_sbox_monomial(idx_monos[sboxes[j][3]][k],x,y)&0x1;
                    mzd_write_bit(mat,j,i*block_size+k,v);
                }
			}

			free(ctx);
		}
	}


	clock_gettime(CLOCK_MONOTONIC,&finish);
	elp = (finish.tv_sec - start.tv_sec);
	elp += (finish.tv_nsec - start.tv_nsec) / 1000000000.0;
	if(prot)
		cout<<"Sample time:"<<elp<<endl;

	for (int i = 0; i < dim_sample; i++)
		mzd_write_bit(mat, i, Nsamples*block_size + i, 1);
	if(prot)
		cout << "Samples Collected" << endl;

	clock_gettime(CLOCK_MONOTONIC,&start);
	mzd_echelonize(mat, 0);
	mzd_t* wnd = mzd_init_window(mat,0,0,dim_sample,Nsamples*block_size);
	int rank=mzd_first_zero_row(wnd);
	mzd_free_window(wnd);
	clock_gettime(CLOCK_MONOTONIC,&finish);
	elp = (finish.tv_sec - start.tv_sec);
	elp += (finish.tv_nsec - start.tv_nsec) / 1000000000.0;
	if(prot){
	cout<<"RREF time:"<<elp<<endl;
	cout<<"Rank:"<<rank<<endl;
	}

	vector<array<int,4>> res;
	for(int i=rank;i<dim_sample;i++){
			for(int j=Nsamples*block_size;j<Nsamples*block_size+dim_sample;j++)
            {
				if(mzd_read_bit(mat,i,j))
				{
                    res.push_back(sboxes[j-Nsamples*block_size]);
					break;
				}
            }

    }
	mzd_free(mat);
	return res;
}

bool sort_fn_asc( const BoolePolynomial& i,const BoolePolynomial& j) { return (i.lead()<j.lead()); }
bool sort_fn_asc_mon( const BooleMonomial& i,const BooleMonomial& j) { return (i<j); }
bool sort_fn_dsc_mon( const BooleMonomial& i,const BooleMonomial& j) { return (i>j); }
//bool sort_fn_dsc_mon( const BoolePolynomial& i,const BoolePolynomial& j) { return (i.lead()>j.lead()); }

vector<BoolePolynomial>
interred(const vector<BoolePolynomial>& eqs);

void DoElimination(list<BoolePolynomial>& lin_eqs,
				    bool forward,
                    const vector<int>& lst_idx,
					const vector<BooleMonomial>& lst_monos,
					const vector<__uint64_t>& ZZ,
                    const int prot=0)
{
	vector<BoolePolynomial> eqs=GenerateSampleMatrix(forward,lst_monos.size()+EXECIVE_SAMPLES,lst_idx,lst_monos,ZZ,prot);
    if(prot)
        cout<<"#lins:"<<eqs.size()<<endl;
    move(eqs.begin(),eqs.end(),inserter(lin_eqs,lin_eqs.end()));
}

void DoEliminationProne(list<BoolePolynomial>& lin_eqs,
                    const vector<int>& lst_idx,
					const vector<BooleMonomial>& lst_monos,
					const vector<__uint64_t>& ZZ_X,
                    const vector<__uint64_t>& ZZ_Y,
                    const int prot=0)
{
	vector<BoolePolynomial> eqs=GenerateSampleMatrixProne(lst_monos.size()+EXECIVE_SAMPLES,lst_idx,lst_monos,ZZ_X,ZZ_Y,prot);
    if(prot)
        cout<<"#lins:"<<eqs.size()<<endl;
    eqs = interred(eqs);
    move(eqs.begin(),eqs.end(),inserter(lin_eqs,lin_eqs.end()));
}
vector<BooleMonomial> DivisionMons(const vector<BooleVariable>& vars)
{
    vector<BooleMonomial> res;
    int nb = vars.size();
    int num = 0x1<<nb;
    for(int i=1;i<num;i++)
    {
        BooleMonomial m(ring);
        for(int j=0;j<nb;j++)
            if( (0x1<<j)&i)
                m*=vars[j];
        res.push_back(m);
        //cout<<m<<endl;
    }
    return res;
}


bool get_next_mask(string& bitmask) {
	return prev_permutation(bitmask.begin(), bitmask.end());
}

unsigned long long fact(int n) {
	unsigned long long factorial = 1;
	for (int i = 1; i <= n; ++i) {
		factorial *= i;
	}
	return factorial;
}

unsigned long long comb(int n, int k) {
	unsigned long long factorial = 1;
	for (int i = n - k + 1; i <= n; ++i) {
		factorial *= i;
	}

	return (factorial / fact(k));
}


vector<BoolePolynomial>
AllLinAnalysisRbyR(
                  bool forward,
                  const vector<__uint64_t>& ZZ_N,
                  set<BooleMonomial>& excluded_mon,
                  const int prot=0
                  )
{
    vector<BoolePolynomial> eqs;
    vector<int> idxs;
    for(int i=0;i<Nm;i++)
        idxs.push_back(i);
    vector<BooleMonomial> vars;
    cout << __func__ << endl;
    for(int i=LIN_ANALYSIS_START_ROUND;i<=LIN_ANALYSIS_LAST_ROUND;i++)
    {
        vars.clear();
        list<BoolePolynomial> teqs;
        for(int k=0;k<Nm;k++)
		{
            for(int j=0;j<INT_BIT_SIZE;j++)
            {
                if(excluded_mon.find(var_L[k][i][j])==excluded_mon.end())
                    vars.push_back(var_L[k][i][j]);
            }
		}
        if(CONSIDER_KEY_VARS)
        {
            for(int j=GUESS_BITS;j<KeySize;j++)
                vars.push_back(var_Keys[j]);
        }
        vars.push_back(BooleMonomial(ring));
        sort(vars.begin(),vars.end());
        reverse(vars.begin(),vars.end());
        DoElimination(teqs,forward,idxs,vars,ZZ_N,prot);
        move(teqs.begin(),teqs.end(),inserter(eqs,eqs.end()));
        if(prot)
        {
                cout<<"-------------"<<endl;
                cout <<"Rnd: "<<i<<" ,#idxs: "<<idxs.size()<<", #teqs: "<<teqs.size()<<endl;
                cout<<"-------------"<<endl;
        }
    }
    if(prot)
        cout<<"#eqs: "<<eqs.size()<<endl;

    for(auto it=eqs.begin();it!=eqs.end();it++)
        excluded_mon.insert(it->lead());
    return eqs;
}

vector<BoolePolynomial>
AllLinAnalysisTot(
                  bool forward,
                  const vector<__uint64_t>& ZZ_N,
                  set<BooleMonomial>& excluded_mon,
                  const int prot=0
                  )
{
    vector<BoolePolynomial> eqs;
    vector<int> idxs;
    for(int i=0;i<Nm;i++)
        idxs.push_back(i);
    vector<BooleMonomial> vars;
    cout << __func__ << endl;
    for(int i=LIN_ANALYSIS_START_ROUND;i<=LIN_ANALYSIS_LAST_ROUND;i++)
    {

        for(int k=0;k<Nm;k++)
        {
            vector<BooleMonomial> cur_vars;
            for(int j=0;j<INT_BIT_SIZE;j++)
            {
                if(excluded_mon.find(var_L[k][i][j])==excluded_mon.end())
                    cur_vars.push_back(var_L[k][i][j]);
            }
            copy(cur_vars.begin(),cur_vars.end(),inserter(vars,vars.end()));
		}
    }
    if(1)
    {   list<BoolePolynomial> teqs;
        if(CONSIDER_KEY_VARS)
        {
            for(int j=GUESS_BITS;j<KeySize;j++)
                vars.push_back(var_Keys[j]);
        }
        vars.push_back(BooleMonomial(ring));
        sort(vars.begin(),vars.end());
        reverse(vars.begin(),vars.end());
        DoElimination(teqs,forward,idxs,vars,ZZ_N,prot);
        move(teqs.begin(),teqs.end(),inserter(eqs,eqs.end()));
        for(auto it=teqs.begin();it!=teqs.end();it++)
        {
            auto mon = (*it).lead();
            excluded_mon.insert(mon);
            auto vars_it = find(vars.begin(),vars.end(),mon);
            if(vars_it!=vars.end())
                vars.erase(vars_it);
        }

        if(prot)
        {
                cout<<"-------------"<<endl;
                cout <<"Rnd: "<<"All"<<" ,#idxs: "<<idxs.size()<<", #teqs: "<<teqs.size()<<endl;
                cout<<"-------------"<<endl;
        }
    }
    if(prot)
        cout<<"#eqs: "<<eqs.size()<<endl;

    return eqs;
}
vector<BoolePolynomial>
AllLinAnalysisProne(
                  const vector<__uint64_t>& ZZ_X,
                  const vector<__uint64_t>& ZZ_Y,
                  set<BooleMonomial>& excluded_mon,
                  const int prot=0
                  )
{
    vector<BoolePolynomial> eqs;
    vector<int> idxs;
    for(int i=0;i<Nm;i++)
        idxs.push_back(i);
    vector<BooleMonomial> vars;
    cout << __func__ << endl;
    for(int i=LIN_ANALYSIS_START_ROUND;i<=LIN_ANALYSIS_LAST_ROUND;i++)
    {
        vars.clear();
        list<BoolePolynomial> teqs;
        for(int k=0;k<Nm;k++)
		{
            for(int j=0;j<INT_BIT_SIZE;j++)
            {
                if(excluded_mon.find(var_L[k][i][j])==excluded_mon.end())
                    vars.push_back(var_L[k][i][j]);
            }
		}
        if(CONSIDER_KEY_VARS)
        {
            for(int j=GUESS_BITS;j<KeySize;j++)
                vars.push_back(var_Keys[j]);
        }

        vars.push_back(BooleMonomial(ring));
        sort(vars.begin(),vars.end());
        reverse(vars.begin(),vars.end());
        DoEliminationProne(teqs,idxs,vars,ZZ_X,ZZ_Y,prot);
        move(teqs.begin(),teqs.end(),inserter(eqs,eqs.end()));
        if(prot)
        {
                cout<<"-------------"<<endl;
                cout <<"Rnd: "<<i<<" ,#idxs: "<<idxs.size()<<", #teqs: "<<teqs.size()<<endl;
                cout<<"-------------"<<endl;
        }
    }
    if(prot)
        cout<<"#eqs: "<<eqs.size()<<endl;


    for(auto it=eqs.begin();it!=eqs.end();it++)
        excluded_mon.insert(it->lead());
    vars.clear();
    list<BoolePolynomial> teqs;

    for(int i=LIN_ANALYSIS_START_ROUND;i<=LIN_ANALYSIS_LAST_ROUND;i++)
    {

        for(int k=0;k<Nm;k++)
        {
            vector<BooleMonomial> cur_vars;
            for(int j=0;j<INT_BIT_SIZE;j++)
            {
                if(excluded_mon.find(var_L[k][i][j])==excluded_mon.end())
                    cur_vars.push_back(var_L[k][i][j]);
            }
            copy(cur_vars.begin(),cur_vars.end(),inserter(vars,vars.end()));
		}
    }
    if(1)
    {
        if(CONSIDER_KEY_VARS)
        {
            for(int j=GUESS_BITS;j<KeySize;j++)
                vars.push_back(var_Keys[j]);
        }
        vars.push_back(BooleMonomial(ring));
        sort(vars.begin(),vars.end());
        reverse(vars.begin(),vars.end());
        DoEliminationProne(teqs,idxs,vars,ZZ_X,ZZ_Y,prot);
        move(teqs.begin(),teqs.end(),inserter(eqs,eqs.end()));
        for(auto it=teqs.begin();it!=teqs.end();it++)
        {
            auto mon = (*it).lead();
            excluded_mon.insert(mon);
            auto vars_it = find(vars.begin(),vars.end(),mon);
            if(vars_it!=vars.end())
                vars.erase(vars_it);
        }

    }
    if(prot)
        cout<<"#eqs: "<<eqs.size()<<endl;
    return eqs;
}

void
AllLinSboxAnalysisRbyR(
                  bool forward,
                  const vector<__uint64_t>& ZZ_N,
                  bitset<IGNORE_BITSET_SIZE>& ignore_set,
                  const int prot=0
                  )
{

    size_t pos=0;

    char buff[100];
    int count = 0;
    vector<BoolePolynomial> X(SBOX_SIZE,ring_sbox);
    vector<BoolePolynomial> Y(SBOX_SIZE,ring_sbox);
    cout << __func__ << endl;
    for(unsigned int i=0;i<SBOX_SIZE;i++)
    {
        sprintf(buff,"X%d",i);
        ring_sbox.setVariableName(pos,buff);
        X[i] = ring_sbox.variable(pos);
        pos++;

    }
    for(unsigned int i=0;i<SBOX_SIZE;i++)
    {
        sprintf(buff,"Y%d",i);
        ring_sbox.setVariableName(pos,buff);
        Y[i] = ring_sbox.variable(pos);
        pos++;
    }

    vector<BoolePolynomial> eqs= SboxAdd(X,Y);

    vector< array<int,4> > sboxes;
    for(int i=LIN_ANALYSIS_START_ROUND;i<=LIN_ANALYSIS_LAST_ROUND;i++)
    {
        sboxes.clear();
        for(int k=0;k<Nm;k++)
		{
            for(int j=0;j<NUMBER_OF_SBOX_IN_ROUND;j++)
            {
                for(unsigned int l=0;l<eqs.size();l++)
                {
                    array<int,4> a = {k,i,j,l};
                    if(!ignore_set[ToIgnoreSboxIndex(k,i,j,l)])
                        sboxes.push_back(a);
                }
            }
		}
        //verse(sboxes.begin(),sboxes.end());
        auto cur = GenerateSampleSuperMatrix(forward,2*sboxes.size(),sboxes,eqs,ZZ_N,prot);
        if(prot)
        {
                cout<<"-------------"<<endl;
                cout <<"Rnd: "<<i<<" ,#sboxes: "<<sboxes.size()<<", #lids: "<<cur.size()<<endl;
                cout<<"-------------"<<endl;
        }
        count += cur.size();
        for(auto it=cur.begin();it!=cur.end();it++)
        {
            auto a = *it;
            ignore_set[ToIgnoreSboxIndex(a[0],a[1],a[2],a[3])]=true;
        }
    }
    if(prot)
        cout<<"#lids: "<<count<<endl;

    return;
}

void
AllLinSboxAnalysisTot(
                  bool forward,
                  const vector<__uint64_t>& ZZ_N,
                  bitset<IGNORE_BITSET_SIZE>& ignore_set,
                  const int prot=0
                  )
{

    size_t pos=0;

    char buff[100];
    int count = 0;
    vector<BoolePolynomial> X(SBOX_SIZE,ring_sbox);
    vector<BoolePolynomial> Y(SBOX_SIZE,ring_sbox);

    cout << __func__ << endl;
    for(unsigned int i=0;i<SBOX_SIZE;i++)
    {
        sprintf(buff,"X%d",i);
        ring_sbox.setVariableName(pos,buff);
        X[i] = ring_sbox.variable(pos);
        pos++;

    }
    for(unsigned int i=0;i<SBOX_SIZE;i++)
    {
        sprintf(buff,"Y%d",i);
        ring_sbox.setVariableName(pos,buff);
        Y[i] = ring_sbox.variable(pos);
        pos++;
    }

    vector<BoolePolynomial> eqs= SboxAdd(X,Y);

    vector< array<int,4> > sboxes;
    for(int i=LIN_ANALYSIS_START_ROUND;i<=LIN_ANALYSIS_LAST_ROUND;i++)
    {
        for(int k=0;k<Nm;k++)
		{
            for(int j=0;j<NUMBER_OF_SBOX_IN_ROUND;j++)
            {
                for(unsigned int l=0;l<eqs.size();l++)
                {
                    array<int,4> a = {k,i,j,l};
                    if(!ignore_set[ToIgnoreSboxIndex(k,i,j,l)])
                        sboxes.push_back(a);
                }
            }
		}
    }
    if(1)
    {
        //reverse(sboxes.begin(),sboxes.end());
        auto cur = GenerateSampleSuperMatrix(forward,2*sboxes.size(),sboxes,eqs,ZZ_N,prot);
        if(prot)
        {
                cout<<"-------------"<<endl;
                cout <<"Rnd: "<<"All"<<" ,#sboxes: "<<sboxes.size()<<", #lids: "<<cur.size()<<endl;
                cout<<"-------------"<<endl;
        }
        count += cur.size();
        for(auto it=cur.begin();it!=cur.end();it++)
        {
            auto a = *it;
            ignore_set[ToIgnoreSboxIndex(a[0],a[1],a[2],a[3])]=true;
        }
    }
    return;
}

void SinglePassElim(vector<BoolePolynomial>& eqs)
{
  cout << __func__ << endl;
    groebner::ReductionStrategy generators(ring);
    generators.optRedTailDegGrowth = true;
    generators.optRedTail = true;

    for(auto it=eqs.begin();it!=eqs.end();)
    {
        if(it->isZero())
            it=eqs.erase(it);
        else
            it++;
    }
    sort(eqs.begin(),eqs.end(),sort_fn_asc);
    for(auto it=eqs.begin();it!=eqs.end();)
    {
        auto p=generators.nf(*it);
            *it=p;
            if(!p.isZero())
            {
                generators.addGenerator(p);
                it++;
                cout<<p<<endl;
            }
            else
            {
                it=eqs.erase(it);
            }
    }

}
void FastVarElim(
        const vector<BoolePolynomial>& lin_eqs,
        vector<BoolePolynomial>& eqs
        )
{
  cout << __func__ << endl;
    groebner::ReductionStrategy generators(ring);
    generators.optRedTailDegGrowth = true;
    generators.optRedTail = true;

    for(auto it=lin_eqs.begin();it!=lin_eqs.end();it++)
    {
        if(it->length() <= Nm)
        {
            auto p=generators.nf(*it);
            if(!p.isZero())
                generators.addGenerator(p);
        }
    }

    for(auto it=eqs.begin();it!=eqs.end();it++)
    {
            *it= generators.nf(*it);
    }

}

vector<BoolePolynomial> FindOrphanVars(vector<BoolePolynomial>& eqs)
{
    vector<BoolePolynomial> orph_eqs;
    set<BooleMonomial> lead_monos;
    set<BooleMonomial> orph_monos;
    cout << __func__ << endl;
    for(auto it=eqs.begin();it!=eqs.end();it++)
    {
        lead_monos.insert((*it).lead());
    }
    for(auto it=eqs.begin();it!=eqs.end();it++)
    {
        for(auto it_m=it->begin();it_m != it->end();it_m++)
        {
            if(*it_m == it->lead())
                continue;
            BooleMonomial mon = *it_m;
            if(lead_monos.find(mon)!=lead_monos.end())
                orph_monos.insert(mon);
        }
    }

    for(auto it=eqs.begin();it!=eqs.end();it++)
    {
        BooleMonomial mon = it->lead();
        if(it->length() > VARIABLE_ELIMLEN_LIMIT || orph_monos.find(mon)!=orph_monos.end())
            orph_eqs.push_back(*it);

    }
    return orph_eqs;
}


int CheckKey(const bitset<KeySchedSize>& MainKey, vector<BoolePolynomial> res)
{
    int cnt_found_bits=0;
    cout << __func__ << endl;
    for(auto it=res.begin();it!=res.end();it++)
    {
        if(cnt_found_bits>=KeySize)
            return cnt_found_bits;
        if(it->deg()!=1)
            continue;
        auto mon = it->lead();
        BooleVariable v = *mon.variableBegin();
        const char * v_name = ring.getVariableName(v.index());
        if(v_name[0] == 'K')
        {
            int i;
            sscanf(v_name,"K%d",&i);
            if(i<KeySize && ((*it)+MainKey[i]) == it->lead())
            {
                cnt_found_bits++;
            }
            else
            {
                cout<<"::Error in Key "<<i<< " "<<MainKey[i] << "," <<*it<<" ::"<<std::flush;
                break;
            }

        }
    }
    return cnt_found_bits;
}

void GeneratePCSet(void* ctx,vector<__uint64_t>& ZZ_X,
        vector<__uint64_t>& ZZ_Y)
{
  cout << __func__ << endl;
    for(int i=0;i<Nm;i++)
    {
        INT_TYPE tmpVals[Nr][2];
        switch(STRATEGY)
        {
            case CHOSEN_PLAINTEXT:
                ZZ_X[i] = num_to_textpatt(i, patt);
                ZZ_Y[i] = encryptTap(0, ZZ_X[i], ctx, tmpVals);
                break;
            case CHOSEN_CIPHERTEXT:
                ZZ_Y[i] = num_to_textpatt(i, patt);
                ZZ_X[i] = decryptTap(0, ZZ_Y[i], ctx, tmpVals);
                break;
            case KNOWN_PLAINTEXT:
                ZZ_X[i] = Rd64();
                ZZ_Y[i] = encryptTap(0, ZZ_X[i], ctx, tmpVals);
                break;
            case KNOWN_CIPHERTEXT:
                ZZ_Y[i] = Rd64();
                ZZ_X[i] = decryptTap(0, ZZ_Y[i], ctx, tmpVals);
                break;

        }
    }
}

vector<BoolePolynomial> python_mimic_groebner(const vector<BoolePolynomial>& eqs);
vector<BoolePolynomial> python_mimic_groebner_linear_basis(const vector<BoolePolynomial>& eqs);
vector<BoolePolynomial> python_mimic_groebner_prone(const vector<BoolePolynomial>& eqs,const vector<__uint64_t> ZZ_X ,const vector<__uint64_t> ZZ_Y );

void remove_zeros(vector<BoolePolynomial>& eqs){
    for(auto it=eqs.begin();it!=eqs.end();)
    {
        if(it->isZero())
            it=eqs.erase(it);
        else
            it++;
    }
}
void DoExperiment(
        const vector<BoolePolynomial>& forward_eqs,
        const bitset<IGNORE_BITSET_SIZE>& ignore_set,
        const vector<vector<int> >& l_idxs,
        const array< vector<BooleVariable> ,Nm>& var_L_All
        )
{
    timespec start, finish;
    double elp;
    double elp_backelim;
    double elp_slv;
    int num_lins=0;
    vector<BoolePolynomial> eqs;
    vector<BoolePolynomial> fw_eqs=forward_eqs;
    vector<BoolePolynomial> lin_eqs;
    vector<BoolePolynomial> K(KeySize,ring);
	vector<vector<BoolePolynomial> > X(Nm,vector<BoolePolynomial>(64,ring));
	vector<vector<BoolePolynomial> > Y(Nm,vector<BoolePolynomial>(64,ring));
    int num_fw_eqs=0;
    int num_bw_eqs=0;
    int num_pr_eqs=0;


    bitset<KeySchedSize> MainKey;
	for (int j = 0; j < KeySize; j++) {
		MainKey[j] = Rd32() & 0x1;
	}

    for(int j=0;j<GUESS_BITS;j++)
    {
        if(KEY_GUESS_STRATEGY == WRONG_KEY_GUESS)
            GuessedKey[j] = (Rd32() & 0x1);
        else
            GuessedKey[j] = MainKey[j];
    }

	void* ctx = SetKey(Nr, MainKey);
    for(int i=0;i<KeySize;i++)
		K[i]=var_Keys[i];

	vector<__uint64_t> ZZ_Y(Nm);
    vector<__uint64_t> ZZ_X(Nm);

    vector<__uint64_t> ZZ_T1(Nm);
    vector<__uint64_t> ZZ_T2(Nm);

    GeneratePCSet(ctx,ZZ_X,ZZ_Y);
	for(int i=0;i<Nm;i++)
	{
		for(int j=0;j<64;j++)
		{
			X[i][j] = (ToStateXY(ZZ_X[i])>>j)&0x1;
			Y[i][j] = (ToStateXY(ZZ_Y[i])>>j)&0x1;
		}
	}

    if(IS_PLAINTEXT_BASED(STRATEGY))
    {
        ZZ_T1 = ZZ_X;
        ZZ_T2 = ZZ_Y;
    }
    else
    {
        ZZ_T1 = ZZ_Y;
        ZZ_T2 = ZZ_X;
    }
    clock_gettime(CLOCK_MONOTONIC,&start);
    set<BooleMonomial> excluded_mon;
    bitset<IGNORE_BITSET_SIZE> ig_set = ignore_set;
    if(GUESS_BITS>0 || ! IS_CHOSEN_SCENARIO(STRATEGY))
    {
        fw_eqs = AllLinAnalysisRbyR(IS_PLAINTEXT_BASED(STRATEGY),ZZ_T1,excluded_mon,REPORT_PRONE);
        if(POLYNOMIAL_ANALYSIS)
        {
            AllLinSboxAnalysisRbyR(IS_PLAINTEXT_BASED(STRATEGY),ZZ_T1,ig_set,1);
        }

    }
    else
    {
        for(auto it=fw_eqs.begin();it!=fw_eqs.end();it++)
            excluded_mon.insert(it->lead());

    }
    vector<BoolePolynomial> bw_eqs = AllLinAnalysisRbyR(!IS_PLAINTEXT_BASED(STRATEGY),ZZ_T2,excluded_mon,REPORT_PRONE);
    if(POLYNOMIAL_ANALYSIS)
    {
        AllLinSboxAnalysisRbyR(!IS_PLAINTEXT_BASED(STRATEGY),ZZ_T2,ig_set,1);
        AllLinSboxAnalysisTot(IS_PLAINTEXT_BASED(STRATEGY),ZZ_T1,ig_set,1);
        AllLinSboxAnalysisTot(!IS_PLAINTEXT_BASED(STRATEGY),ZZ_T2,ig_set,1);
    }


    vector<BoolePolynomial> fw_eqs_tot = AllLinAnalysisTot(IS_PLAINTEXT_BASED(STRATEGY),ZZ_T1,excluded_mon,REPORT_PRONE);
    vector<BoolePolynomial> bw_eqs_tot = AllLinAnalysisTot(!IS_PLAINTEXT_BASED(STRATEGY),ZZ_T2,excluded_mon,REPORT_PRONE);
    vector<BoolePolynomial> prone_eqs = AllLinAnalysisProne(ZZ_X,ZZ_Y,excluded_mon,REPORT_PRONE);

    num_fw_eqs = fw_eqs.size()+fw_eqs_tot.size();
    num_bw_eqs = bw_eqs.size()+bw_eqs_tot.size();
    num_pr_eqs = prone_eqs.size();
    if(GUESS_BITS>0 || ! IS_CHOSEN_SCENARIO(STRATEGY))
    {
        move(fw_eqs.begin(),fw_eqs.end(),inserter(lin_eqs,lin_eqs.end()));
    }
    else
    {
        copy(fw_eqs.begin(),fw_eqs.end(),inserter(lin_eqs,lin_eqs.end()));
    }

    if(!FORWARD_ONLY)
    {
        move(fw_eqs_tot.begin(),fw_eqs_tot.end(),inserter(lin_eqs,lin_eqs.end()));
        move(bw_eqs.begin(),bw_eqs.end(),inserter(lin_eqs,lin_eqs.end()));
        move(bw_eqs_tot.begin(),bw_eqs_tot.end(),inserter(lin_eqs,lin_eqs.end()));
        move(prone_eqs.begin(),prone_eqs.end(),inserter(lin_eqs,lin_eqs.end()));
    }
    num_lins = lin_eqs.size();

    vector<BoolePolynomial> orph_eqs = FindOrphanVars(lin_eqs);

    cout<<NumVars<<" "<<num_lins<<" "<<num_fw_eqs<<" "<<num_bw_eqs<<" "<<num_pr_eqs<<" "<<orph_eqs.size()<<" "<<std::flush;

    clock_gettime(CLOCK_MONOTONIC,&finish);
  elp = (finish.tv_sec - start.tv_sec);
  elp += (finish.tv_nsec - start.tv_nsec) / 1000000000.0;
    elp_backelim = elp;

    AIOEncryptEqs(eqs,lin_eqs,ig_set,K,X,Y);
    move(orph_eqs.begin(),orph_eqs.end(),inserter(eqs,eqs.end()));

    for(int i=0;i<GUESS_BITS;i++)
    {
        BoolePolynomial p = var_Keys[i];
        p+=(GuessedKey[i]?1:0);
        eqs.push_back(p);
    }
    remove_zeros(eqs);
    cout<<eqs.size()<<" ::"<<count_if (eqs.begin(), eqs.end(), [](const BoolePolynomial& p){return !p.isZero();})<<":: "<<elp_backelim<<std::flush;

    clock_gettime(CLOCK_MONOTONIC,&start);
    vector<BoolePolynomial> res = python_mimic_groebner(eqs);

    clock_gettime(CLOCK_MONOTONIC,&finish);
	elp = (finish.tv_sec - start.tv_sec);
	elp += (finish.tv_nsec - start.tv_nsec) / 1000000000.0;
	elp_slv=elp;

	cout<<" "<< elp_slv<<" "<<res.size()<<" "<<CheckKey(MainKey,res)<<endl;

    if(PRINT_KEY)
    {
        cout<<"-------------------"<<endl;
        for(int i=0;i<KeySize;i++)
            cout<<MainKey[i]<<",";
        cout<<endl;
        for(auto it=res.begin();it!=res.end();it++)
        {
            auto mon = it->lead();
            if(any_of(mon.variableBegin(),mon.variableEnd(),[](const BooleVariable& v){return (ring.getVariableName(v.index())[0]=='K');}))
                cout<<*it<<",";

        }
        cout<<endl;
        cout<<"-------------------"<<endl;
    }
}



int main() {
	char buff[100];

    vector<vector<int> > l_idxs;
	vector<BoolePolynomial> fw_eqs;
    bitset<IGNORE_BITSET_SIZE> ignore_set;
	array< vector<BooleVariable> ,Nm> var_L_All;
	size_t pos=0;

    for(int i=0;i<Nm;i++)
    {
            str_L[i].resize(Nr);
    }


    if(ring.ordering().isBlockOrder())
    {
        cout <<"Using Block Ordering"<<endl;


        for(int i=Nm-1;i>=0;i--)
        {
            //
            //for(int i=0;i<Nm;i++)
            for(int j=LIN_ANALYSIS_START_ROUND;j<=LIN_ANALYSIS_LAST_ROUND;j++)
            {
                for(int k=0;k<INT_BIT_SIZE;k++){
                    sprintf(buff,"L_%d_%d_%d",i,j,k);
                    str_L[i][j][k] = buff;
                    ring.setVariableName(pos,str_L[i][j][k].c_str());
                    var_L[i][j][k] = ring.variable(pos);
                    var_L_All[i].push_back(var_L[i][j][k]);
                    pos++;
                }
            }
            ring.ordering().appendBlock(pos);
        }

        for(unsigned int i=0;i<str_Keys.size();i++)
        {
            sprintf(buff,"K%.3d",i);
            ring.setVariableName(pos,buff);
            var_Keys[i]=ring.variable(pos);
            pos++;
        }
        ring.ordering().appendBlock(pos);


    }
    else
    {
        for(unsigned int i=0;i<str_Keys.size();i++)
        {
            sprintf(buff,"K%.3d",i);
            ring.setVariableName(pos,buff);
            var_Keys[i]=ring.variable(pos);
            pos++;
        }

        for(int j=LIN_ANALYSIS_START_ROUND;j<=LIN_ANALYSIS_LAST_ROUND;j++)
        {
            for(int i=0;i<Nm;i++)
            {
                for(int k=0;k<INT_BIT_SIZE;k++){
                    sprintf(buff,"L_%d_%d_%d",i,j,k);
                    str_L[i][j][k] = buff;
                    ring.setVariableName(pos,str_L[i][j][k].c_str());
                    var_L[i][j][k] = ring.variable(pos);
                    var_L_All[i].push_back(var_L[i][j][k]);
                    pos++;
                }
            }
        }

    }



    cout<<ring<<endl;

    cout<< (IS_CHOSEN_SCENARIO(STRATEGY)?"Chosen":"Known")<<" "<<(IS_PLAINTEXT_BASED(STRATEGY)?"Plaintext":"Ciphertext")<<" Scenario"<<endl;
    if(IS_CHOSEN_SCENARIO(STRATEGY))
    {

        cout<<"Pattern: ";
        for(unsigned int i=0;i<patt.size();i++)
            cout<<patt[i]<<" ";
        cout<<endl;
    }

    if(CONSIDER_KEY_VARS)
            cout<<"Recovering polynomials with key variables"<<endl;

    if(GUESS_BITS > 0)
    {
        if(KEY_GUESS_STRATEGY == WRONG_KEY_GUESS)
            cout<<"Wrong Key Guess Startegy.";
        else
            cout<<"Right Key Guess Startegy.";
        cout <<" #Guess : "<< GUESS_BITS <<endl;
    }
    cout << "Running Attack for "<<CIPHER_STRING<<"-"<<Nr<<"-"<<Nm<<"-AllLin"<<endl;

    if(CHECK_ENCRYPT_EQS)
    {
        vector<vector<BoolePolynomial> > X(Nm,vector<BoolePolynomial>(64,ring));
        vector<vector<BoolePolynomial> > Y(Nm,vector<BoolePolynomial>(64,ring));
        cout<<"Check equation system"<<endl;
        timespec start, finish;
        double elp;
        bitset<KeySchedSize> MainKey;


        for (int j = 0; j < KeySize; j++) {
            MainKey[j] = Rd32() & 0x1;
        }

        void* ctx = SetKey(Nr, MainKey);
        vector<BoolePolynomial> K(KeySize,ring);
        for(int i=0;i<KeySize;i++)
            K[i]=(int)MainKey[i];

        vector<__uint64_t> ZZ_Y(Nm);
        vector<__uint64_t> ZZ_X(Nm);

        GeneratePCSet(ctx,ZZ_X,ZZ_Y);
        for(int i=0;i<Nm;i++)
        {
            for(int j=0;j<64;j++)
            {
                X[i][j] = (ToStateXY(ZZ_X[i])>>j)&0x1;
                Y[i][j] = (ToStateXY(ZZ_Y[i])>>j)&0x1;
            }
        }
        vector<BoolePolynomial> eqs;
        vector<BoolePolynomial> lin_eqs;
        clock_gettime(CLOCK_MONOTONIC,&start);
        AIOEncryptEqs(eqs,lin_eqs,ignore_set,K,X,Y);
        vector<BoolePolynomial> res = python_mimic_groebner(eqs);
        clock_gettime(CLOCK_MONOTONIC,&finish);
        elp = (finish.tv_sec - start.tv_sec);
        elp += (finish.tv_nsec - start.tv_nsec) / 1000000000.0;
        cout<<"System check time:"<<elp<<endl;
        if(res.size() <=1)
        {
            cout<<"Contradiction in polynomial system"<<endl;
            return 0;
        }
        else
        {
            bool fully_consistant = true;
            for(auto it=res.begin();it!=res.end();it++)
            {
                if(it->deg()!=1)
                {
                    fully_consistant=false;
                    break;
                }
            }
            if(fully_consistant)
                cout<<"Polynomial system is consistant"<<endl;
            else
                cout<<"Polynomial system is not fully consistant"<<endl;
        }

    }

    if(GUESS_BITS==0 && IS_CHOSEN_SCENARIO(STRATEGY))
    {
        vector<__uint64_t> ZZ_N(Nm);
        for(int i=0;i<Nm;i++)
        {
            ZZ_N[i] = num_to_textpatt(i, patt);
        }

        timespec start, finish;
        double elp;
        set<BooleMonomial> excluded_mon;
        ///*
        cout<<"Elimination of variables in "<< (IS_PLAINTEXT_BASED(STRATEGY)? "Forward" : "Backward")<< " Direction."<<endl;
        clock_gettime(CLOCK_MONOTONIC,&start);
        fw_eqs = AllLinAnalysisRbyR(IS_PLAINTEXT_BASED(STRATEGY),ZZ_N,excluded_mon,REPORT_PRONE);
        if(POLYNOMIAL_ANALYSIS)
        {
            AllLinSboxAnalysisRbyR(IS_PLAINTEXT_BASED(STRATEGY),ZZ_N,ignore_set,1);
        }
        clock_gettime(CLOCK_MONOTONIC,&finish);
        elp = (finish.tv_sec - start.tv_sec);
        elp += (finish.tv_nsec - start.tv_nsec) / 1000000000.0;
        cout<<"Elimination time:"<<elp<<endl;
    }

    for(int i=0;i<NumTest;i++)
    {
        //if(fork()==0)
        {
            cout << i <<": ";
            DoExperiment(fw_eqs,ignore_set,l_idxs,var_L_All);
            //exit(0);
        }
        /*
        else
        {
           waitpid(-1,NULL,0);
        }*/
    }
    cout<<ring<<endl;
    return 0;
}

static std::vector<BoolePolynomial> someNextDegreeSpolys(groebner::GroebnerStrategy& strat, unsigned int n){
    std::vector<BoolePolynomial> res;
    assert(!(strat.pairs.pairSetEmpty()));
    strat.pairs.cleanTopByChainCriterion();
    groebner::deg_type deg=strat.pairs.queue.top().sugar;

    while((!(strat.pairs.pairSetEmpty())) &&
                (strat.pairs.queue.top().sugar<=deg) && (res.size()<n)){
        //assert(strat.pairs.queue.top().sugar==deg);
        res.push_back(strat.nextSpoly());
        strat.pairs.cleanTopByChainCriterion();
    }
    return res;
}


static int steps(int size) {
  return (size > 100? 10 : (size >10? 30: 100));
}

vector<BoolePolynomial>
ElimLin(const vector<BoolePolynomial>& eqs){
    vector<BoolePolynomial> result = eqs;
    bool isChanged=true;
    if(eqs.size()==0)
        return result;
    for(auto it=result.begin();it!=result.end();)
    {
        if(it->isZero())
            it=result.erase(it);
    }

    while(isChanged)
    {
        isChanged=false;
        sort(result.begin(),result.end(),sort_fn_asc);
        map<BooleMonomial,BoolePolynomial> lead_map;
        for(auto it=result.begin();it!=result.end();)
        {
            BoolePolynomial p = *it;
            BoolePolynomial pp=p;
            for(auto it_m = p.begin();it_m!= p.end();it_m++)
            {
                BooleMonomial mon = *it_m;
                auto it_p = lead_map.find(mon);
                if(it_p!=lead_map.end())
                {
                    pp+=it_p->second;
                }
            }

            if(pp != p)
            {
                *it=pp;
                /*cout<<p<<endl;
                cout<<"--"<<endl;
                cout<<pp<<endl;
                cout<<"-------------"<<endl;*/
                isChanged = true;
            }
            if(pp.isZero())
            {
                it=result.erase(it);
            }
            else
            {
                if(lead_map.find(pp.lead())==lead_map.end())
                    lead_map.insert(pair<BooleMonomial,BoolePolynomial>(pp.lead(),pp));
                it++;
            }

        }
    }

    return result;
}


vector<BoolePolynomial>
interred(const vector<BoolePolynomial>& eqs){
    vector<BoolePolynomial> result = eqs;
    bool isChanged=true;
    if(eqs.size()==0)
        return result;
    for(auto it=result.begin();it!=result.end();)
    {
        if(it->isZero())
            it=result.erase(it);
        else
            it++;
    }
    if(result.size()==0)
        return result;
    while(isChanged)
    {
        isChanged=false;
        groebner::ReductionStrategy generators(ring);
        generators.optRedTailDegGrowth = true;
        generators.optRedTail = true;
        sort(result.begin(),result.end(),sort_fn_asc);
        for(auto it=result.begin();it!=result.end();it++)
        {
            BoolePolynomial p = generators.nf(*it);
            if(!isChanged && p != (*it))
                isChanged = true;
            if( ! p.isZero() )
            {
                generators.addGenerator(p);
            }
        }
        if(isChanged)
        {
            result.clear();
            for(auto it=generators.begin();it != generators.end(); it++)
                result.push_back((*it).p);
        }
    }

    return result;
}


vector<BoolePolynomial>  easy_linear_polynomials_via_interpolation(const BoolePolynomial& p)
{
    vector<BoolePolynomial> res;
    auto p_vars = p.usedVariables();
    auto space = p_vars.divisors();
    auto zeros = groebner::zeros(p,space);
    auto lex_leads = groebner::variety_lex_leading_terms(zeros, p_vars);
    for(auto it =lex_leads.begin();it!=lex_leads.end();it++)
    {
       auto m=*it;
         if(m.deg()==1)
         {
             auto red = m + groebner::nf_lex_points(m,zeros);
             if(red != p && red.leadDeg() <= p.leadDeg() )
                res.push_back(red);
         }
    }
    return res;
}
vector<BoolePolynomial> easy_linear_polynomials(const BoolePolynomial& p)
{
    vector<BoolePolynomial> res;
    if(p.deg()>=2)
    {
        if(p.usedVariables().deg() > 8)
        {
            auto opp = p + 1;
            auto ftrs = groebner::easy_linear_factors(opp);
            for(auto it=ftrs.begin();it!=ftrs.end();it++)
                res.push_back((*it) + 1);
        }
        else
            res = easy_linear_polynomials_via_interpolation(p);
    }
    return res;
}

vector<BoolePolynomial> python_mimic_groebner(const vector<BoolePolynomial>& eqs)
{
    const double max_growth = 2.0;
    const int selection_size = 10000;
    //const double pair_size_factor = 2.0;
    int count_keys=0;


    groebner::GroebnerStrategy strat(ring);
	strat.generators.optRedTail = true;
	strat.enabledLog = REPORT_GROBNER;
	strat.optLazy = true;
	strat.optExchange = true;
	strat.generators.optLL = false;
	strat.optAllowRecursion = false;
	strat.optLinearAlgebraInLastBlock = false;
	strat.optModifiedLinearAlgebra = false;
	strat.optDrawMatrices = false;
	strat.generators.optRedTailDegGrowth=true;
	strat.reduceByTailReduced = false;
    for(auto it=eqs.begin();it!=eqs.end();it++)
    {
        strat.addGeneratorDelayed(*it);
    }

    while(strat.pairs.queue.size() > 0 && count_keys < (NumKeys)) {
        int cur_deg = strat.pairs.queue.top().sugar;
        //bool contains_key_lead=false;
        std::vector<BoolePolynomial> ps =
        someNextDegreeSpolys(strat, selection_size);

        int min_deg = 10000;
        for(unsigned int i=0;i<ps.size();i++)
        {
            //if(!ps[i].isZero())
            //    cout<<ps[i].lead()<<","<<ps[i].length()<<endl;
            ps[i] = groebner::cheap_reductions(strat.generators,ps[i]);
        }
        //cout<<"---------------------"<<endl;
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
            {
                if(ps[i].deg() < min_deg)
                    min_deg = ps[i].deg();
            }
        }
        std::vector<BoolePolynomial> nw_ps;
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
            {
                if((ps[i].deg() <= min_deg) || ring.ordering().isBlockOrder())
                    nw_ps.push_back(ps[i]);
                else
                    strat.addGeneratorDelayed(ps[i]);
            }
        }

        if(strat.enabledLog)
        {
            cout<<"Current Degree: "<<cur_deg<<" , Min Degree: "<<min_deg<<endl;
            cout<< "( "<< strat.pairs.queue.size()<<" )"<<endl;
            cout<< "start reducing"<<endl;
            cout<<"(Chain Crit. : "<<strat.chainCriterions<<", VC: "<<strat.
                    variableChainCriterions<<", EASYP: "<< strat.
                    easyProductCriterions<<", EXTP: "<<strat.
                    extendedProductCriterions<<")"<<endl;
            cout<< nw_ps.size()<<" spolys added"<<endl;
        }
        ps =
        parallel_reduce(nw_ps, strat, steps(nw_ps.size()), max_growth);
        min_deg = 100000;
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
                if(ps[i].deg() < min_deg)
                    min_deg = ps[i].deg();
        }
        nw_ps.clear();
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
            {
                auto p = ps[i];
                if(ps[i].deg() <= min_deg)
                    nw_ps.push_back(ps[i]);
                else
                    strat.addGeneratorDelayed(ps[i]);
            }
        }
        sort(nw_ps.begin(),nw_ps.end(),sort_fn_asc);

        for(auto it=nw_ps.begin(); it != nw_ps.end() ;it++){
            auto p = *it;
            strat.addAsYouWish(p);
            if(strat.enabledLog)
            {
                cout<<"(Result:, deg: "<<p.deg()<<", lm: "<< p.lead()<<", el: "<<p.length()<<")"<<  endl;
                cout<<"#Generators: "<<strat.generators.size()<<endl;
            }
            auto mon = p.lead();
            if(p.deg()==1 && any_of(mon.variableBegin(),mon.variableEnd(),[](const BooleVariable& v){return (ring.getVariableName(v.index())[0]=='K');}))
            {
                count_keys++;
            }

        }
        strat.cleanTopByChainCriterion();
    }
    return strat.minimalizeAndTailReduce();
}


vector<BoolePolynomial> python_mimic_groebner_linear_basis(const vector<BoolePolynomial>& eqs)
{
    const double max_growth = 2.0;
    const int selection_size = 10000;
    //const double pair_size_factor = 2.0;
    int count_keys=0;

    groebner::ReductionStrategy lin_red_gens(ring);
    vector<BooleMonomial>       lin_leads;
    bool swLinGensChanged=false;

    groebner::GroebnerStrategy strat(ring);
	strat.generators.optRedTail = true;
	strat.enabledLog = REPORT_GROBNER;
	strat.optLazy = true;
	strat.optExchange = true;
	strat.generators.optLL = false;
	strat.optAllowRecursion = false;
	strat.optLinearAlgebraInLastBlock = false;
	strat.optModifiedLinearAlgebra = false;
	strat.optDrawMatrices = false;
	strat.generators.optRedTailDegGrowth=true;
	strat.reduceByTailReduced = false;
    for(auto it=eqs.begin();it!=eqs.end();it++)
    {
        strat.addGeneratorDelayed(*it);
    }

    while(strat.pairs.queue.size() > 0 && count_keys < (NumKeys)) {
        swLinGensChanged = false;
        int cur_deg = strat.pairs.queue.top().sugar;
        //bool contains_key_lead=false;
        std::vector<BoolePolynomial> ps =
        someNextDegreeSpolys(strat, selection_size);

        int min_deg = 10000;
        for(unsigned int i=0;i<ps.size();i++)
        {
            //if(!ps[i].isZero())
            //    cout<<ps[i].lead()<<","<<ps[i].length()<<endl;
            ps[i] = groebner::cheap_reductions(strat.generators,ps[i]);
        }
        //cout<<"---------------------"<<endl;
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
            {
                if(ps[i].deg() < min_deg)
                    min_deg = ps[i].deg();
            }
        }
        std::vector<BoolePolynomial> nw_ps;
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
            {
                if((ps[i].deg() <= min_deg))
                    nw_ps.push_back(ps[i]);
                else
                    strat.addGeneratorDelayed(ps[i]);
            }
        }

        if(strat.enabledLog)
        {
            cout<<"Current Degree: "<<cur_deg<<" , Min Degree: "<<min_deg<<endl;
            cout<< "( "<< strat.pairs.queue.size()<<" )"<<endl;
            cout<< "start reducing"<<endl;
            cout<<"(Chain Crit. : "<<strat.chainCriterions<<", VC: "<<strat.
                    variableChainCriterions<<", EASYP: "<< strat.
                    easyProductCriterions<<", EXTP: "<<strat.
                    extendedProductCriterions<<")"<<endl;
            cout<< nw_ps.size()<<" spolys added"<<endl;
        }
        ps =
        parallel_reduce(nw_ps, strat, steps(nw_ps.size()), max_growth);
        min_deg = 100000;
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
                if(ps[i].deg() < min_deg)
                    min_deg = ps[i].deg();
        }
        nw_ps.clear();
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
            {
                auto p = ps[i];
                if(ps[i].deg() <= min_deg)
                    nw_ps.push_back(ps[i]);
                else
                    strat.addGeneratorDelayed(ps[i]);
            }
        }
        sort(nw_ps.begin(),nw_ps.end(),sort_fn_asc);

        for(auto it=nw_ps.begin(); it != nw_ps.end() ;it++){
            auto p = *it;
            strat.addAsYouWish(p);
            if(strat.enabledLog)
            {
                cout<<"(Result:, deg: "<<p.deg()<<", lm: "<< p.lead()<<", el: "<<p.length()<<")"<<  endl;
                cout<<"#Generators: "<<strat.generators.size()<<endl;
            }
            auto mon = p.lead();
            if(p.deg()==1 && any_of(mon.variableBegin(),mon.variableEnd(),[](const BooleVariable& v){return (ring.getVariableName(v.index())[0]=='K');}))
            {
                count_keys++;
            }
            if(p.deg()==1)
            {
                lin_red_gens.addGenerator(p);
                lin_leads.push_back(p.lead());
                swLinGensChanged = true;
            }

        }
        strat.cleanTopByChainCriterion();
        //Check Leading Terms With Linear Basis
        if(swLinGensChanged)
        {
            vector<groebner::PairE> holder;
            vector<BoolePolynomial> new_polys;
            while(strat.pairs.queue.size() > 0)
            {
                auto pair = strat.pairs.queue.top();
                strat.pairs.queue.pop();
                if(pair.getType() == groebner::DELAYED_PAIR && any_of(lin_leads.begin(),lin_leads.end(),[pair](const BooleMonomial& v){return (pair.lm.reducibleBy(v));}))
                {
                    auto p = lin_red_gens.nf(pair.delayedPair().p);
                    if(!p.isZero())
                    {
                        new_polys.push_back(p);
                        if(strat.enabledLog)
                        {
                            BoolePolynomial p1(ring);
                            BoolePolynomial p2(ring);
                            p1 = pair.delayedPair().p.lead();
                            p2 = p.lead();
                            cout<<"----"<<p1<<","<<p2<<"----"<<endl;
                        }
                    }
                }
                else
                    holder.push_back(pair);

            }
            while(holder.size()>0){
                strat.pairs.queue.push(holder.back());
                holder.pop_back();
            }
            while(new_polys.size()>0)
            {
                strat.addGeneratorDelayed(new_polys.back());
                new_polys.pop_back();
            }
        }
        //Check Leading Terms With Linear Basis

    }
    return strat.minimalizeAndTailReduce();
}


vector<BoolePolynomial> python_mimic_groebner_prone(const vector<BoolePolynomial>& eqs,const vector<__uint64_t> ZZ_X ,const vector<__uint64_t> ZZ_Y )
{
    const double max_growth = 2.0;
    const int selection_size = 10000;
    //const double pair_size_factor = 2.0;


    set<BooleMonomial> excluded_mon;
  	groebner::GroebnerStrategy strat(ring);
	strat.generators.optRedTail = true;
	strat.enabledLog = true;
	strat.optLazy = true;
	strat.optExchange = true;
	strat.generators.optLL = false;
	strat.optAllowRecursion = false;
	strat.optLinearAlgebraInLastBlock = false;
	strat.optModifiedLinearAlgebra = false;
	strat.optDrawMatrices = false;
	strat.generators.optRedTailDegGrowth=true;
	strat.reduceByTailReduced = false;
    for(auto it=eqs.begin();it!=eqs.end();it++)
    {
        strat.addGeneratorDelayed(*it);
    }
    vector<int> idxs;
    for(int i=0;i<Nm;i++)
        idxs.push_back(i);

    while(strat.pairs.queue.size() > 0) {
        int cur_deg = strat.pairs.queue.top().sugar;
        //bool contains_key_lead=false;
        std::vector<BoolePolynomial> ps =
        someNextDegreeSpolys(strat, selection_size);

        int min_deg = 10000;
        for(unsigned int i=0;i<ps.size();i++)
        {
            //if(!ps[i].isZero())
            //    cout<<ps[i].lead()<<","<<ps[i].length()<<endl;
            ps[i] = groebner::cheap_reductions(strat.generators,ps[i]);
        }
        //cout<<"---------------------"<<endl;
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
            {
                if(ps[i].deg() < min_deg)
                    min_deg = ps[i].deg();
            }
        }
        std::vector<BoolePolynomial> nw_ps;
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
            {
                if((ps[i].deg() <= min_deg))
                    nw_ps.push_back(ps[i]);
                else
                    strat.addGeneratorDelayed(ps[i]);
            }
        }

        if(strat.enabledLog)
        {
            cout<<"Current Degree: "<<cur_deg<<" , Min Degree: "<<min_deg<<endl;
            cout<< "( "<< strat.pairs.queue.size()<<" )"<<endl;
            cout<< "start reducing"<<endl;
            cout<<"(Chain Crit. : "<<strat.chainCriterions<<", VC: "<<strat.
                    variableChainCriterions<<", EASYP: "<< strat.
                    easyProductCriterions<<", EXTP: "<<strat.
                    extendedProductCriterions<<")"<<endl;
            cout<< nw_ps.size()<<" spolys added"<<endl;
        }
        ps =
        parallel_reduce(nw_ps, strat, steps(nw_ps.size()), max_growth);
        min_deg = 100000;
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
                if(ps[i].deg() < min_deg)
                    min_deg = ps[i].deg();
        }
        nw_ps.clear();
        for(unsigned int i=0;i<ps.size();i++)
        {
            if(! ps[i].isZero())
            {
                auto p = ps[i];
                if(ps[i].deg() <= min_deg)
                    nw_ps.push_back(ps[i]);
                else
                    strat.addGeneratorDelayed(ps[i]);
            }
        }
        sort(nw_ps.begin(),nw_ps.end(),sort_fn_asc);



        for(auto it=nw_ps.begin(); it != nw_ps.end() ;it++){
            auto p = *it;
            strat.addAsYouWish(p);
            excluded_mon.insert(p.lead());
            if(strat.enabledLog)
            {
                cout<<"(Result:, deg: "<<p.deg()<<", lm: "<< p.lead()<<", el: "<<p.length()<<")"<<  endl;
                cout<<"#Generators: "<<strat.generators.size()<<endl;
            }
        }
        set<BooleMonomial> monos;
        vector<BooleMonomial> lst_monos;
        for(auto it=nw_ps.begin(); it != nw_ps.end() ;it++){
            auto p = *it;
            for(auto it=p.begin();it!=p.end();it++)
            {
                auto mon=*it;
                if(any_of(mon.variableBegin(),mon.variableEnd(),[](const BooleVariable& v){return (ring.getVariableName(v.index())[0]=='K');}))
                {
                    continue;
                }
                if(excluded_mon.find(mon)==excluded_mon.end())
                    monos.insert(mon);
            }
        }
        for(auto it=monos.begin();it!=monos.end();it++)
            lst_monos.push_back(*it);
        list<BoolePolynomial> aug_eqs;
        if(lst_monos.size()>0)
            DoEliminationProne(aug_eqs,idxs,lst_monos,ZZ_X,ZZ_Y,1);
        for(auto it=aug_eqs.begin();it!=aug_eqs.end();it++)
        {
            auto p = groebner::cheap_reductions(strat.generators,*it);
            if(!p.isZero())
                strat.addGeneratorDelayed(p);

        }
        strat.cleanTopByChainCriterion();
    }
    return strat.minimalizeAndTailReduce();
}
