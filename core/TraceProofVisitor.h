#ifndef _G_TRACE_PROOF_VISITOR_H_
#define _G_TRACE_PROOF_VISITOR_H_

#include "glucose/core/ProofVisitor.h"
#include "glucose/core/Solver.h"

#include <cstdio>

namespace Glucose
{
 class TraceProofVisitor : public ProofVisitor
 {
 protected:
   Solver &m_Solver;
   CMap<int> m_visited;

   vec<int> m_units;
   int m_ids;
   FILE *m_out;
   
   void doAntecendents ();
   
 public:
   TraceProofVisitor (Solver &solver, FILE* out);
   
   int visitResolvent (Lit parent, Lit p1, CRef p2);
   int visitChainResolvent (Lit parent);
   int visitChainResolvent (CRef parent);
 };
}
#endif
