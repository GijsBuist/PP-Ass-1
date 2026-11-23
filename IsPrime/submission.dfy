// Please, before you do anything else, add your names here:
// Group:    9
// Member 1: Gijs Laurens Marie Buist: 2130459
// Member 2: Sanula De Silva: 2088509

include "assignment.dfy"
 
/*
 * OPTIMISATION: only odd divisors (other than 2) are checked.
 *
 * Solution: n <= 1 and even n are handled before the loop (2 is the only even
 * prime). n is then odd, so no even number can divide it, and d starts at 3
 * and steps by 2.
 *
 * Proof: the invariant "no k with 1 < k < d divides n" is kept from the naive
 * version. When d becomes d + 2, k = d was just tested and k = d + 1 is even,
 * so it cannot divide the odd n (the assert in the loop). On exit d == n, so
 * the invariant gives prime(n).
 */ 
module Submission refines Assignment {
    // Note that while you CAN remove this time limit, we will put it back when
    // we start grading. Please leave it in and use it as a guide. Submissions
    // that time out are considered wrong.
    @TimeLimit(60)
    method IsPrime(n: int) returns (b: bool)
      ensures b <==> prime(n) // repeated for your convenience
    {
       if n <= 1 {
        return false;
       }
       if n == 2 {
        return true;
       }
       if n % 2 == 0 {
        return false;
       }

      // n is odd and >= 3, so only odd divisors need to be checked
      var d := 3;
      while d < n
        invariant 3 <= d <= n
        invariant d % 2 == 1
        invariant forall k :: 1 < k < d ==> n % k != 0
      {
          if n % d == 0 {
            return false;
          }
          // d + 1 is even, so it can't divide the odd number n
          assert n % (d + 1) != 0 by {
            if n % (d + 1) == 0 {
              var j := (d + 1) / 2;     // d+1 is even, so d+1 == 2*j
              var m := n / (d + 1);     // if it divided n, then n == (d+1)*m
              var t := j * m;
              assert d + 1 == 2 * j;
              assert n == (d + 1) * m;
              assert n == 2 * t;        // so n is even: contradiction with n % 2 != 0
            }
          }
          d := d + 2;
      }
      return true;
    }
}