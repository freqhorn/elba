add_executable (elba BoundSolver.cpp)
target_link_libraries (elba ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB} ${ARMADILLO_LIBRARIES})
install(TARGETS elba RUNTIME DESTINATION bin)
