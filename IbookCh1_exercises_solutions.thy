theory IbookCh1_exercises_solutions
  imports Main
begin

lemma evens5:
  fixes k::nat
  shows "\<exists> n . 2*n > k"
proof -
  show ?thesis by presburger
qed

(* next proof doesn't actually work; uncomment it to see,
and then add the comment markers back again *)
(*
lemma "dominate": " 2* (n::nat) + 1 > n + 1"
  by presburger
*) 


lemma "dominate2":
  fixes n::nat
  assumes "n > 0"
  shows "2 * n + 1 > n + 1"
  sorry

lemma "silly":
  fixes n::nat and k
  assumes "n > 3" and "k > 5"
  shows "n+k > 8" and "2*n + k > 11"
proof -
  show "8 < n + k" using assms by auto
  show "11 < 2*n + k" using assms by auto
qed


typedecl r (* proxy for reals *) 
consts
plus::"r \<Rightarrow> r \<Rightarrow> r"
times::"r \<Rightarrow> r \<Rightarrow> r"
neg::"r \<Rightarrow> r"
reciprocal::"r \<Rightarrow> r"
Z :: r (* proxy for zero *)
U :: r (* proxy for one *)

notation plus  (infix "\<oplus>" 80) 
notation times  (infix "\<odot>" 80) 

lemma plus_assoc: (* Spivak calls this P1 *)
  fixes a::r and b::r and c::r
  shows "(a \<oplus> b) \<oplus> c =  a \<oplus> (b \<oplus> c)"
  sorry

(* "The statement of this property clearly renders a separate concept 
of the sum of three numbers superfluous; we simple agree that a + b + c
denotes the number a + (b + c) = (a + b) + c. Addition of four numbers
requires similar, although slightly more involved, considerations. The 
symbol a + b + c + d is defined to mean
   (1) ((a + b) + c) + d,
or (2) (a + (b + c)) + d, 
or (3) (a + ((b+c) + d), or
   ...
This definition is unambiguous since these numbers are all equal. Fortunately, 
THIS fact need not be listed separately, since it follows from the property
P1 already listed. For example, we know from P1 that 
   (a + b) + c = a + (b  + c),
and it follows immediately that (1) and (2) are equal.
*)
(* jfh: here's an example of the kind of assertion and proof that you'll be 
providing for subsequent claims by Spivak *)
lemma ex0: 
  fixes a::r and b::r and c::r and d::r
  shows "((a \<oplus> b) \<oplus> c) \<oplus> d =  (a \<oplus> (b \<oplus> c)) \<oplus> d"
proof -
  show ?thesis using plus_assoc by auto
qed
(* jfh: in the example above, Isabelle was able to guess that it should
apply the associative law to the sum of a, b, and c; in more complicated
cases, we may have to nudge it a little bit. *)

(* The equality of
(2) and (3) is a direct consequence of P1, although this may not be apparent
at first sight (one must let b+c play the role of b in P1, and d the role 
of c). The equalities (3) = (4) = (5) are also simple to prove. 
*)

(* EXERCISE 1: show that (2) = (3) as described. *)

lemma ex1: 
  fixes a::r and b::r and c::r and d::r
  shows "(a \<oplus> (b \<oplus> c)) \<oplus> d =  a \<oplus> ((b \<oplus> c) \<oplus> d)"
proof -
  show ?thesis using plus_assoc by auto
qed
(*

[[omitted discussion of sums of 5 or more numbers]]
The number zero has one property so important that we list it next:

*)
lemma additive_ident: (* Spivak calls this P2 *)
  fixes a::r
  shows "a \<oplus> Z =  a" and "Z \<oplus> a =  a"
  sorry

(* jfh: this is a case where I've put two conclusions in one "shows",
because I wanted to match Spivak's naming scheme *)
(* 
An important role is also played by 0 in the third property of our list:
*)
lemma negation: (* Spivak calls this P3 *)
  fixes a::r
  shows "a \<oplus> (neg a) =  Z"
  and  "(neg a) \<oplus> a =  Z"
  sorry

(*
Property P3 ought to represent a distinguishing characteristic of the
number 0, and it is comforting to note that we are already in a position to 
prove this. Indeed, if a number x satisfies a + x = a for any one 
number a, then x = 0 (and consequently this equation also holds
for all numbers a). The proof of this assertion involves nothing
more than subtracting a from both sides of the equation, in other words,
adding -a to both sides; as the following detailed proof shows, all
three properties P1 - P3 must be used to justify this operation.
     if                 a + x = a
     then        (-a) + (a+x) = (-a) + a = 0;
     hence    ((-a) + a) + x) = 0;
     hence          0    + x  = 0;
     hence                 x  = 0.
*)

(* EXERCISE 2: Formulate the theorem above, and write the proof. *)
lemma ex2: 
  fixes a::r and x
  assumes "a \<oplus> x =  a"
  shows "x =  Z"
proof -
  have 0: "(neg a) \<oplus> (a \<oplus> x) = ((neg a) \<oplus> a)" using assms by auto
  have 1: "(neg a) \<oplus> (a \<oplus> x) = Z"    using [[simp_trace]] using 0 negation by auto
  have 2: "((neg a)\<oplus> a) \<oplus> x = Z" using [[simp_trace]] 1 plus_assoc by auto
  have 3: "Z \<oplus> x = Z" using 2 negation by auto
  show ?thesis using 3 additive_ident by auto
qed

(* As we have just hinted, it is convenient to regard 
subtraction as an operation derived from addition; we consider
a - b to be an abbreviation for a + (-b). 
*)

definition diff:: "r \<Rightarrow> r \<Rightarrow> r" where
"diff a b \<equiv> (a \<oplus> (neg b))"

notation diff  (infix "\<ominus>" 80) 

(*
It is then possible to find
the solutions to certain simple equations by a serious of steps
(each justified by P1, P2, or P3) similar to the ones just presented 
for the equation a + x = a. For example
    If                x + 3 = 5,
    then     (x + 3) + (-3) = 5 + (-3); 
    hence    x + (3 + (-3)) = 5 - 3 = 2;
    hence             x + 0 = 2;
    hence                 x = 2.
*)

(*
Naturally, such elaborate solutions are of interest only until you
become convinced that they can always be supplied. in practice, it is
usually just a waste of time to solve an equation by indicating so 
explicitly the reliance on properties P1, P2, and P3 (or any of
the further properties we shall list).
*)

(* EXERCISE 3: Spivak has an advantage over us here: for him the numbers
3 and 5 already exist, and his readers know that 5 - 3 = 2. We lack 
explicit constants for any numbers except Z and U. We can still, however,
mimic this computation, just in greater generality. Show that
if x + a = b, then x = b - a, following Spivak's computation. *)

lemma ex3: 
  fixes x::r and a and b
  assumes "x \<oplus> a = b"
  shows "x = b \<ominus> a"

proof -
  have 0: "x \<oplus> a = b" using assms by auto
  have 1: "(x \<oplus> a) \<oplus> (neg a) = b \<oplus> (neg a)" using 0 by auto
  have 2: "(x \<oplus> a) \<oplus> (neg a) = x \<oplus> (a \<oplus> (neg a))" using plus_assoc by auto
  have 3: "x \<oplus> (a \<oplus> (neg a)) = b \<oplus> (neg a)" using 1 2 by auto
  have 4: "x \<oplus> Z = b \<oplus> (neg a)" using 3 negation(1) by auto
  have 5: "x = b \<oplus> (neg a)" using 4 additive_ident(1) by auto
  show ?thesis using 5 diff_def by auto
qed

(* Only one other property of addition remains to be listed. When 
considering the sums of three numbers a, b, and c, only two sums 
were mentioned: (a+b) + c and a + (b + c). Actually, several other
arrangements are obtained if the order of a, b, and c is changed. That
these sums are equal depends on 
   (P4) If and and b are any numbers, then 
             a + b = b + a.
*)

lemma plus_commute:
  fixes a::r and b::r 
  shows "(a \<oplus> b) =  (b \<oplus> a)"
  sorry

(* The statement of P4 is meant to emphasize that although the 
operation of addition of pair of numbers might conceivably
depend on the order of the two numbers, in fact it does not. It 
is helpful to remember that not all operations are so well behaved. 
For example, subtraction does not have this property: usually a-b 
 \<noteq> b - a. In passing we might ask just when a = b does equal b-a, and it 
is amusing to discover how powerless we are if we rely only on 
properties P1-P4 to justify our manipulations. Algebra of the most
elementary variety shows that a - b = b - a only when a = b. 
Nevertheless it is impossible to derive this fact from properties 
P1--P4. We will indeed be able to justify all steps in detail when
a few more properties are listed. Oddly enough, however, the 
crucial property involves multiplication. 
*)

(* Math EXERCISE 4: try to check this. See if you can find a 
2-element set and a commutative, associative "addition" operation on it,
with an identity and a negation operation, but which does NOT satisfy  
"(b \<ominus> a = a \<ominus> b) \<Longrightarrow> (a = b)". Hint: Consider items p and q with 
q + q = q, but all other additions producing p.
*)

(*
The basic properties of multiplication are fortunately so similar to those
for addition that little comment will be needed; both the meaning and the 
consequences should be clear. (As in elementary algebra, the product
of a and b will be denoted by  a \<cdot> b, or simple ab.)

  (P5) if a, b, and c are any numbers, then 
       a \<cdot> (b  \<cdot> c) =  (a \<cdot> b)  \<cdot> c.

  (P6) If a is any numbers, then 
        a \<cdot> 1 =  1 \<cdot> a = a. Moreover 1 \<noteq> 0. 

(The assertion that 1 \<noteq> 0 may seem a strange fact to list, but we have to list
it, because there is no way it could possibly be proved on the basis of the
other properties listed--these properties would all hold if there were 
only one number, namely, 0.)

  (P7) For every number a \<noteq> 0, there is a number a^{-1} such that

          a \<cdot> a^{-1} = a^{-1} \<cdot> b = U.

  (P8) If a and b are numbers, then
           a \<cdot> b =  b \<cdot> a
*)
lemma mul_assoc: (* P5 *)
  fixes a::r and b::r and c::r
  shows "((a \<odot> b) \<odot> c) =  (a \<odot> (b \<odot> c))"
  sorry

(* EXERCISE 5: Write P6 (giving it the name 'mul_ident' as a lemma, using 
'sorry' as a proof; mimic the format of prior property-lemmas. Be
sure to include three separate conclusions in your "shows" line. *)
lemma mul_ident:  (* P6 *)
  fixes a::r
  shows "a \<odot> U =  a" and "U \<odot> a =  a" and "Z \<noteq> U"
  sorry

lemma inversion: (* P7 *)
  fixes a::r
  assumes "a \<noteq> Z"
  shows "a \<odot> (reciprocal a) =  U" and "(reciprocal a) \<odot>  a =  U"
  sorry

lemma mul_commute: (* P8 *)
  fixes a::r and b::r 
  shows "(a \<odot> b) =  (b \<odot> a)"
  sorry

lemma distrib:
  fixes a::r and b::r and c::r
  shows "(a \<odot> (b \<oplus> c)) =  ((a \<odot> b) \<oplus> (a \<odot> c))"
  sorry

(* 
One detail which deserves emphasis is the appearance of the condition
a \<noteq> 0 in P7. This condition is quite necessary; since 0 \<cdot> b = 0 for 
all numbers b, there is no number 0^{-1} satisfying 0 \<cdot> 0^{-1} = 1. 
This restriction has an important consequence for division. Just as 
subtraction was defined in terms of addition, so division is defined
in terms of multiplication: the symbol a/b means a \<cdot> b^{-1}. Since 
0^{-1} is meaningless---division by 0 s ALWAYS undefined. 
*)

(*jfh: This is a place where Isabelle and other proof assistants diverge
from conventional mathematical practice. They actually define the 
multiplicative inverse as a function on ALL real numbers. But they
assert nothing about the value of 0^{-1} -- so nothing can be proved 
about it. This takes some getting used to. We use the "reciprocal" 
function to denote the multiplicative inverse *)

(* Property P7 has two important consequences. If a \<cdot> b = a \<cdot> c, it 
does not necessarily follow that b = c; for if a = 0, then both a \<cdot> b
and a \<cdot> c are 0, no matter what b and c are. However, if a \<noteq> 0,
then b = c; this can be deduced from P7 as follows:

  If                 a \<cdot> b = a \<cdot> c and a \<noteq> 0,
  then     a^{-1} \<cdot> (a \<cdot> b) = a^{-1} \<cdot> (a \<cdot> c);
  hence    (a^{-1} \<cdot> a) \<cdot> b = (a^{-1} \<cdot> a) \<cdot> c;
  hence               1 \<cdot> b = 1 \<cdot> c;
  hence                  b = c.
*)

(* EXERCISE 6: mimic the proof above in Isabelle, using "inv" as the 
multiplicative inverse. Make sure to carefully note where you use the 
fact that a is nonzero. This is an example of why it doesn't matter 
if an inverse for 0 is 'defined' ... if it cannot be used for anything!
*)


lemma ex6: 
  fixes a::r and b and c
  assumes "a \<odot> b = a  \<odot> c" and "a \<noteq> Z"
  shows "b = c"
proof -
  have 0: "a \<odot> b = a  \<odot> c" using assms by auto
  have 1: "(reciprocal a) \<odot> (a \<odot> b) = (reciprocal a) \<odot> (a  \<odot> c)" 
    using 0 by auto
  have 2: "((reciprocal a) \<odot> a) \<odot> b = ((reciprocal a) \<odot> a)  \<odot> c" 
    using 1 mul_assoc by auto
  have 3: "U \<odot> b = U  \<odot> c" using 2 inversion(2) assms by auto
  show ?thesis using 3 mul_ident by auto
qed

(* It is also a consequence of P7 that if a \<cdot> b = 0, then either
a = 0 or b = 0. In fact, 

  if                a \<cdot> b = 0 and a \<noteq> 0,
  then    a^{-1} \<cdot> (a \<cdot> b) =  0;
  hence   (a^{-1} \<cdot> a) \<cdot> b =  0;
  hence             1 \<cdot> b = 0; 
  hence                b = 0.

(It may happen that a = 0 and b = 0 are both true; this possibility is
not excluded when we say "either a = 0 or b = 0"; in mathematics, "or"
is always used in the sense of "one or the other, or both.")
*)
(*
EXERCISE 7: Mimic that last proof in Isabelle, trying to copy the structure
of the "cases" proof near the end of Chapter 0. Use
   proof cases ("a = 0")
You may find yourself wanting to prove a preparatory lemma (I did). 
*)
(*  \<oplus>  \<odot>  *)
lemma ex7a: 
  fixes a::r
  shows "a \<odot> Z = Z"
proof -
  have 0: "Z \<oplus> Z = Z" using additive_ident by auto
  have 1: " a \<odot> (Z \<oplus> Z) = a \<odot> Z" using 0 by auto
  have 2: " (a \<odot> Z) \<oplus> (a \<odot> Z) = a \<odot> Z" using 1 distrib by auto
  show ?thesis  using 2 ex2 by blast
qed

lemma ex7:
  fixes a::r and b
  assumes "a \<odot> b = Z" 
  shows "(a = Z) \<or> (b = Z)"
proof (cases "a = Z")
  case True
  then show ?thesis by auto
next
  case False
  have 0: "a \<odot> b = Z" using assms by auto
  have 1: "(reciprocal a) \<odot> (a \<odot> b) = (reciprocal a) \<odot> Z" 
    using 0 by auto
  have 2: "((reciprocal a) \<odot> a) \<odot> b = Z" 
    using 1 mul_assoc ex7a by auto
  have 3: "U \<odot> b = Z" using 2 inversion False by auto
  have 4: " b = Z" using 3 mul_ident  by auto
  then show ?thesis using 4 by auto
qed

(* remainder deleted, as there were no more exercises for students after this point *)


end
