/*
 * ProofVisitor.h
 *
 * Proof traversal functionality.
 *
 *  Created on: Jan 4, 2014
 *      Author: yakir
 */

#ifndef G_PROOF_VISITOR_H_
#define G_PROOF_VISITOR_H_

#include "glucose/core/SolverTypes.h"

namespace Glucose {

class ProofVisitor
{
public:
    ProofVisitor() {}
  virtual ~ProofVisitor () {}
  

    virtual int visitResolvent      (Lit parent, Lit p1, CRef p2) { return 0; }
    virtual int visitChainResolvent (Lit parent)                  { return 0; }
    virtual int visitChainResolvent (CRef parent)                 { return 0; }

    vec<Lit>        chainPivots;
    vec<CRef>       chainClauses;
};

}

#endif /* G_PROOF_VISITOR_H_ */
