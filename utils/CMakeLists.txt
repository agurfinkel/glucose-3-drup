add_library (glucose_utils OBJECT  Options.cc System.cc)

install (FILES Options.h ParseUtils.h System.h 
  DESTINATION include/glucose/utils)