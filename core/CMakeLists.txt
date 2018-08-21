add_library (glucose_core.LIB OBJECT Solver.cc TraceProofVisitor.cc)
set_target_properties (glucose_core.LIB PROPERTIES OUTPUT_NAME "glucose_core")

install (FILES Solver.h SolverTypes.h 
  BoundedQueue.h Constants.h Dimacs.h 
  ProofVisitor.h TraceProofVisitor.h
  DESTINATION include/glucose/core)
