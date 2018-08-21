project(Glucose)
cmake_minimum_required(VERSION 2.8.6)

if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR ) 
  message (FATAL_ERROR
    "In-source builds are not allowed. Please clean your source tree and try again.")  
endif()

# prefer linking with static libraries
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})


# check for rt lib. Not needed on OSX.
find_library(RT_LIB NAMES rt)
if (NOT RT_LIB)
  set(RT_LIB "")
endif()
mark_as_advanced(RT_LIB)

include ("cmake/PackageOptions.cmake")
include_directories ("${GLUCOSE_INCLUDE_DIR}")

configure_file (utils/Options.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/utils/Options.h COPYONLY)
configure_file (utils/ParseUtils.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/utils/ParseUtils.h COPYONLY)
configure_file (utils/System.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/utils/System.h COPYONLY)

configure_file (mtl/Alg.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/mtl/Alg.h COPYONLY)
configure_file (mtl/Alloc.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/mtl/Alloc.h COPYONLY)
configure_file (mtl/Heap.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/mtl/Heap.h COPYONLY)
configure_file (mtl/IntTypes.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/mtl/IntTypes.h COPYONLY)
configure_file (mtl/Map.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/mtl/Map.h COPYONLY)
configure_file (mtl/Queue.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/mtl/Queue.h COPYONLY)
configure_file (mtl/Sort.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/mtl/Sort.h COPYONLY)
configure_file (mtl/Vec.h 
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/mtl/Vec.h COPYONLY)
configure_file (mtl/XAlloc.h
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/mtl/XAlloc.h COPYONLY)

configure_file (core/BoundedQueue.h
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/core/BoundedQueue.h COPYONLY)
configure_file (core/Constants.h
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/core/Constants.h COPYONLY)
configure_file (core/Dimacs.h
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/core/Dimacs.h COPYONLY)
configure_file (core/Solver.h
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/core/Solver.h COPYONLY)
configure_file (core/SolverTypes.h
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/core/SolverTypes.h COPYONLY)
configure_file (simp/SimpSolver.h
  ${CMAKE_CURRENT_BINARY_DIR}/include/glucose/simp/SimpSolver.h COPYONLY)


add_subdirectory(utils)
add_subdirectory(core)
add_subdirectory(simp)
add_subdirectory(mtl)

add_library(glucose.LIB STATIC 
  $<TARGET_OBJECTS:glucose_utils>
  $<TARGET_OBJECTS:glucose_core.LIB>
  $<TARGET_OBJECTS:glucose_simp>)

set_target_properties(glucose.LIB 
  PROPERTIES OUTPUT_NAME "glucose")


add_executable (glucose simp/Main.cc)
target_link_libraries (glucose glucose.LIB z)

add_executable(glucose_core core/Main.cc)
target_link_libraries (glucose_core glucose.LIB z)

install (TARGETS glucose.LIB glucose glucose_core
  RUNTIME DESTINATION bin
  ARCHIVE DESTINATION lib)
