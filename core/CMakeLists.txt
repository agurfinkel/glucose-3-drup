add_library (glucose_core.LIB OBJECT Solver.cc )
set_target_properties (glucose_core.LIB PROPERTIES OUTPUT_NAME "glucose_core")

install (FILES Solver.h SolverTypes.h 
  BoundedQueue.h Constants.h Dimacs.h 
  DESTINATION include/glucose/core)
