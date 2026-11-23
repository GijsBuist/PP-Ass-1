// Please, before you do anything else, add your names here:
// Group:    9
// Member 1: Gijs Laurens Marie Buist: 2130459
// Member 2: Sanula De Silva: 2088509

include "assignment.dfy"
 
/**
    Make sure this file and the file tests.dfy verify.
    Verification of tests.dfy is only dependent on the contract of this method, 
    not on its implementation. 
 */
module Submission refines Assignment {
    // Note that while you CAN remove this time limit, we will put it back when
    // we start grading. Please leave it in and use it as a guide. Submissions
    // that time out are considered wrong.
    @TimeLimit(60)
    method LongestBoringSubsequence(a: seq<int>) returns (start: int, len: int)
      // postcondition repeated for your convenience  
      ensures 0 <= start <= start + len <= |a|
      ensures isBoring(a, start, start+len)
      ensures forall i, j :: 0 <= i <= j <= |a| && isBoring(a, i, j) ==> j - i <= len // Boring subsequence may not be longer than sequence.
    {
        start, len := 0, 0;
        var curStart, i := 0, 0;

        while i < |a|
            invariant 0 <= curStart <= i <= |a|
            invariant i == 0 || curStart < i
            invariant curStart == 0 || a[curStart-1] != a[curStart]
            invariant isBoring(a, curStart, i)
            invariant 0 <= start <= start + len <= i
            invariant isBoring(a, start, start + len)
            invariant forall p, q :: 0 <= p <= q <= i && isBoring(a, p, q) ==> q - p <= len
        {
            if i > 0 && a[i] == a[i-1] {
                // run extends, curStart stays
            } else {
                curStart := i;
            }
            i := i + 1;

            if i - curStart > len {
                start, len := curStart, i - curStart;
            }
        }
    }
}
