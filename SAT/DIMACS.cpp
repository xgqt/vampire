/**
 * @file DIMACS.cpp
 * Implements class DIMACS.
 */


#include <iostream>
#include <fstream>

#include "../Lib/List.hpp"
#include "../Lib/Stack.hpp"

#include "DIMACS.hpp"

namespace SAT
{

using namespace std;
using namespace Lib;

void DIMACS::outputProblem(SATClauseList* clauses, ostream& out)
{
  unsigned cnt=0;
  unsigned maxVar=0;

  {
    SATClauseList::Iterator cit(clauses);
    while(cit.hasNext()) {
      cnt++;
      SATClause* cl=cit.next();
      unsigned clen=cl->length();
      for(unsigned i=0;i<clen;i++) {
	ASS_G((*cl)[i].var(),0);
	if((*cl)[i].var()>maxVar) {
	  maxVar=(*cl)[i].var();
	}
      }
    }
  }
  out<<"p cnf "<<maxVar<<"  "<<cnt<<endl;

  SATClauseList::Iterator cit(clauses);
  while(cit.hasNext()) {
    SATClause* cl=cit.next();
    out<<cl->toDIMACSString()<<endl;
  }
  out<<"0"<<endl;
}

SATClauseIterator DIMACS::parse(const char* fname, unsigned& maxVar)
{
  CALL("DIMACS::parse");

  istream* inp0;

  if(fname) {
    inp0=new ifstream(fname);
  } else {
    inp0=&cin;
  }

  istream& inp=*inp0;
  if(!inp.good()) {
    cout<<"Cannot open file\n";
    exit(0);
  }

  char buf[512];
  char ch;
  inp>>ch;
  while(ch=='c') {
    inp.getline(buf,512);
    inp>>ch;
  }
  ASS_EQ(ch,'p');
  for(int i=0;i<3;i++) {
    inp>>ch;
  }

  SATClauseList* res=0;

  unsigned remains;
  int ivar;
  Stack<int> vars(64);
  inp>>maxVar;
  inp>>remains;
  while(remains--) {
    inp>>ivar;
    while(ivar!=0) {
      if(inp.eof()) {
	cout<<"Invalid input\n";
	exit(0);
      }
      vars.push(ivar);
      inp>>ivar;
    }
    unsigned clen=(unsigned)vars.size();
    SATClause* cl=new(clen) SATClause(clen, true);
    for(int i=(int)clen-1; i>=0;i--) {
      ivar=vars.pop();
      (*cl)[i].set(abs(ivar), ivar>0);
    }
    ASS(vars.isEmpty());

    cl->sort();
    SATClauseList::push(cl,res);
  }

  if(inp0!=&cin) {
    delete inp0;
  }

  return pvi( SATClauseList::DestructiveIterator(res) );
}


}
