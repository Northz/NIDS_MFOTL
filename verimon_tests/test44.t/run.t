  $ monpoly -verified -sig test44.sig -formula test44_1.mfotl -log test44_1.log -verbose
  The analyzed formula is:
    p(x) SINCE[2,2] q(x)
  The sequence of free variables is: (x)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @1 (time point 1): ()
  At time point 2:
  @2 (time point 2): ()

  $ monpoly -verified -sig test44.sig -formula test44_2.mfotl -log test44_2.log -verbose
  The analyzed formula is:
    p(x) SINCE[1,*) q(x)
  The sequence of free variables is: (x)
  At time point 0:
  @0 (time point 0): ()
  At time point 1:
  @1 (time point 1): ((1))
  At time point 2:
  @2 (time point 2): ()
