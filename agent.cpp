#include<iostream>
#include<string>
#include<vector>
#include<fstream>


using namespace std;

class Clause;
class Predicate;
void MakePredicate(string, Clause *, bool);
bool OrSearch(Predicate, vector<string> &);

vector<Clause> gClauseList;


class Predicate {

public:

	string name;
	string farg;
	string sarg;
	int    argnumber;
	int    vararg;									//If 1. denotes firstarg is x 2. means second 0 means none...it is a fact.

	Predicate()
	{
		name		= "";
		farg		= "";
		sarg		= "";
		vararg		= -1;
		argnumber	= 0;
	}


	Predicate(string pname, string pfarg, string psarg, int pvararg, int pargn)
	{
		name		= pname;
		farg		= pfarg;
		sarg		= psarg;
		argnumber	= pargn;
		vararg		= pvararg;
	}

	Predicate(Predicate const &pred)
	{
		name		= pred.name;
		farg		= pred.farg;
		sarg		= pred.sarg;
		vararg		= pred.vararg;
		argnumber	= pred.argnumber;
	
	}

	bool Match(Predicate & pPred, string & psubsitute)
	{
		if (pPred.name.compare(name) != 0 || (pPred.argnumber != argnumber))
			return false;

		if ((pPred.vararg == 1 && vararg == 2) || (pPred.vararg == 2 && vararg == 1))
			return false;

		if (argnumber == 1 && (vararg == 1 || pPred.farg.compare(farg) == 0)) {
			if (vararg  == 1)
				psubsitute = pPred.farg;
			return true;
		
		}
		else {

			if (vararg == 1 && pPred.sarg.compare(sarg) == 0) {
				psubsitute = pPred.farg;
				return true;
			}

			if (vararg == 2 && pPred.farg.compare(farg) == 0) {
				psubsitute = pPred.sarg;
				return true;
			}

			if (vararg == 0 && (pPred.sarg.compare(sarg) == 0 || pPred.vararg == 2) && (pPred.vararg == 1 || pPred.farg.compare(farg) == 0)) {
				if (pPred.vararg == 2)
				{
					psubsitute = sarg;
				}

				if (pPred.vararg == 1) {
					psubsitute = farg;
				}
				return true;
			}
		}
		
		return false;
		
	}

		

};

class Clause
{

public:

	vector<Predicate>	RHS;
	vector<Predicate>	LHS;
	bool				IsFact;
	bool                isunified;

	Clause()
	{
		isunified = false;
	}

	~Clause()
	{
		RHS.clear();
		LHS.clear();
	}
	
	
	vector<Predicate> * DoSubsitutions(string pStr)
	{
		vector<Predicate>::iterator it = LHS.begin();

		vector<Predicate> * mylist = new vector<Predicate> ;

		while (it != LHS.end()) 
		{
			Predicate mypred;

			mypred.argnumber = it->argnumber;
			mypred.farg = it->farg;
			mypred.name = it->name;
			mypred.sarg = it->sarg;
			mypred.vararg = it->vararg;

			if (!pStr.empty()) {

				if (mypred.vararg == 1)
					mypred.farg = pStr;

				if (mypred.vararg == 2)
					mypred.sarg = pStr;

				mypred.vararg = 0;

				

			}

			mylist->push_back(mypred);

			++it;

		}

		return mylist;
	}


};


void MakeClause(string pline)
{
	Clause myclause;

	size_t pos	=	pline.find("=>");

	if (pos == string::npos) {

		myclause.IsFact = true;
		MakePredicate(pline, &myclause, true);
	
	} else {
			
		myclause.IsFact = false;

		string pright	=	pline.substr(pos + 2, string::npos);
		string pleft	=	pline.substr(0, pos);

		MakePredicate(pright, &myclause, true);

		//Now parse pleft for &
		size_t found = pleft.find("&");
		
		//only single predicate on lhs
		if (found == string::npos) {
			MakePredicate(pleft, &myclause, false);
			goto End;
		}
		else
		{
			size_t start = 0;
			
			do {

				MakePredicate(pleft.substr(start, found - start), &myclause, false);

				start = found + 1;

				found = pleft.find("&", found + 1);


			} while (found != string::npos);

			//add the last clause
			MakePredicate(pleft.substr(start, string::npos), &myclause, false);
			
		}
		
	}

End:
	gClauseList.push_back(myclause);
	
}


void MakePredicate(string pline, Clause * pclause, bool pisright)
{
	Predicate mypred("", "", "", 0, 0);

	//Setting predicate name
	size_t	pos		=	pline.find("(");      // position of "(" in str
	string	name	=	pline.substr(0, pos);
	mypred.name		=	name;

	//Getting argument list
	size_t	pos1	=	pline.find("(");
	size_t	pos2	=	pline.find(")");
	string	arglist =	pline.substr(pos1 + 1, pos2 - 1 - pos1);

	if (arglist.find(",") != string::npos) {
	
		mypred.argnumber = 2;
		
		size_t	pos		=	arglist.find(",");
		mypred.farg		=	arglist.substr(0, pos);
		mypred.sarg		=	arglist.substr(pos + 1, string::npos);

		if (mypred.farg.compare("x") == 0)
			mypred.vararg = 1;

		if (mypred.sarg.compare("x") == 0)
			mypred.vararg = 2;
				
	} else {

		mypred.argnumber = 1;

		mypred.farg = arglist;
		
		if (mypred.farg.compare("x") == 0)
			mypred.vararg = 1;

	
	}

	

	if (pisright)
		pclause->RHS.push_back(mypred);
	else
		pclause->LHS.push_back(mypred);
	

}

Predicate * MakeSinglePredicate(string pline)
{
	Predicate *  mypred = new Predicate("", "", "", 0, 0);

	//Setting predicate name
	size_t	pos		= pline.find("(");      // position of "(" in str
	string	name	= pline.substr(0, pos);
	mypred->name	= name;

	//Getting argument list
	size_t	pos1	= pline.find("(");
	size_t	pos2	= pline.find(")");
	string	arglist = pline.substr(pos1 + 1, pos2 - 1 - pos1);

	if (arglist.find(",") != string::npos) {

		mypred->argnumber = 2;

		size_t	pos  = arglist.find(",");
		mypred->farg = arglist.substr(0, pos);
		mypred->sarg = arglist.substr(pos + 1, string::npos);

		if (mypred->farg.compare("x") == 0)
			mypred->vararg = 1;

		if (mypred->sarg.compare("x") == 0)
			mypred->vararg = 2;

	}
	else {

		mypred->argnumber = 1;

		mypred->farg = arglist;

		if (mypred->farg.compare("x") == 0)
			mypred->vararg = 1;


	}


	return mypred;
	

}


bool AndSearch(vector<Predicate> pList)
{
	bool result			= true;
	

	if (pList.empty())
		return true;

	vector<Predicate>::iterator it = pList.begin();

	vector<string> sublist;

	do {

		if (it == pList.end())
			return true;

		result = OrSearch(*it, sublist);

		if (!result)
			return false;

		++it;

	} while (sublist.empty());

	vector<string>::iterator iter = sublist.begin();
	
	vector<Predicate>::iterator rest = it;


	while (iter != sublist.end()) {

		rest = it;
		bool flag = true;
		while (rest != pList.end())
		{

			Predicate mypred;

			mypred.argnumber = rest->argnumber;
			mypred.farg = rest->farg;
			mypred.name = rest->name;
			mypred.sarg = rest->sarg;
			mypred.vararg = rest->vararg;

			if (mypred.vararg != 0) {

				if (mypred.vararg == 1)
					mypred.farg = *iter;
				else
					mypred.sarg = *iter;

			}

			mypred.vararg = 0;

			vector<string> dummy;

			result = OrSearch(mypred, dummy);

			//case subsitution did not work
			if (!result) {

				flag = false;
				break;

			}

			++rest;
		}

		//subsitution worked
		if (flag)
			return true;

		++iter;

	}

	
	return false;

}

bool OrSearch(Predicate queryPredicate, vector<string> & sublist)
{
	string		subsitute = "";
	Clause		tempclause;
	Predicate	temppredicate;
	bool		result = false;
	bool        finalresult = false;
	vector<Clause>::iterator it = gClauseList.begin();
	

	//loop through all clauses' RHS
	while (true && it != gClauseList.end()) {

		temppredicate = it->RHS.front();

		subsitute = "";

		//if query matches
		if (temppredicate.Match(queryPredicate, subsitute) && !it->isunified) {
			////case: it matched a fact
			//if (temppredicate.vararg == 0 && it->IsFact) {
			//	subsitutenew = subsitute;
			//	return true;
			//}
			vector<Predicate> * mylist = new vector<Predicate>;

			//only if rhs had a scope for subsitution
			mylist = it->DoSubsitutions(temppredicate.vararg ? subsitute : "");

			it->isunified = true;

			//call and search on all lhs
			result = AndSearch((*mylist));

			it->isunified = false;

			//if (queryPredicate.vararg == 0 && result)
			//	return true;

			finalresult = result | finalresult;

			if (result && !subsitute.empty() && queryPredicate.vararg != 0)
				sublist.push_back(subsitute);

			mylist->clear();
			
			
		}

		subsitute = "";
		++it;

	}

	return finalresult;
			
}


bool GetResult(Predicate queryPredicate)
{
	vector<string> mylist;
	return OrSearch(queryPredicate, mylist);


}


int main()
{

	fstream		myfile, ofile;								
	long long	number;										
	string		clause_str;									
	string		query_str;									
	

	//open the file in read mode
	myfile.open("input.txt", fstream::in | fstream::out);

	//Reads type of algorithm.
	myfile >> query_str;

	Predicate queryPredicate = *MakeSinglePredicate(query_str);

	//Read the number of clause
	myfile >> number;

	//make clauses
	for (int i = 0; i < number; ++i) {
		//read the name
		myfile >> clause_str;
		//push into vector
		MakeClause(clause_str);

	}

	myfile.close();

	ofile.open("output.txt", fstream::out);

	bool result = false; 
	
	result = GetResult(queryPredicate);
	
	if (result)
		ofile << "TRUE";
	else
		ofile << "FALSE";
	
	ofile.close();

	gClauseList.clear();


}







