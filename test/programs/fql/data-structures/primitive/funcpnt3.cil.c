/* Generated by CIL v. 1.3.7 */
/* print_CIL_Input is true */

#line 7 "funcpnt3.c"
struct test1 {
   int x ;
   void (*pnt)() ;
};
#line 2 "funcpnt3.c"
void test(void) 
{ int x ;

  {
#line 4
  x = 3;
#line 5
  return;
}
}
#line 12 "funcpnt3.c"
int main(void) 
{ struct test1 lab ;
  struct test1 *k ;
  unsigned int __cil_tmp3 ;
  unsigned int __cil_tmp4 ;
  unsigned int __cil_tmp5 ;
  unsigned int __cil_tmp6 ;
  void (*__cil_tmp7)() ;

  {
#line 15
  k = & lab;
#line 16
  __cil_tmp3 = (unsigned int )k;
#line 16
  __cil_tmp4 = __cil_tmp3 + 4;
#line 16
  *((void (**)())__cil_tmp4) = & test;
#line 17
  __cil_tmp5 = (unsigned int )k;
#line 17
  __cil_tmp6 = __cil_tmp5 + 4;
#line 17
  __cil_tmp7 = *((void (**)())__cil_tmp6);
#line 17
  (*__cil_tmp7)();
#line 20
  return (0);
}
}
