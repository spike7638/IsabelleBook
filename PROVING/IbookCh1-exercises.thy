theory "IbookCh1-exercises"
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
  have 1: "(neg a) \<oplus> (a \<oplus> x) = Z"  using 0 negation by auto
  have 2: "((neg a)\<oplus> a) \<oplus> x = Z" using 1 plus_assoc by auto
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
 \<noteq> b - a. In passing we might ask just when a - b does equal b-a, and it 
is amusing to discover how powerless we are if we rely only on 
properties P1-P4 to justify our manipulations. Algebra of the most
elementary variety shows that a - b = b - a only when a = b. 
Nevertheless it is impossible to derive this fact from properties 
P1--P4. We will indeed be able to justify all steps in detail when
a few more properties are listed. Oddly enough, however, the 
crucial property involves multiplication. 
*)

(* Spivak says we can't prove this yet, but can Isabelle do so perhaps? 
Let's see! Uncomment the following and look what's produced; then add 
back the comment markers *)
(*
lemma not_yet:
  fixes a::r and b::r
  assumes "a \<ominus> b = b \<ominus> a"
  shows "a = b"
  try
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
of a and b will be denoted by  a \<cdot> b, or simply ab.)

  (P5) if a, b, and c are any numbers, then 
       a \<cdot> (b  \<cdot> c) =  (a \<cdot> b)  \<cdot> c.

  (P6) If a is any numbers, then 
        a \<cdot> 1 =  1 \<cdot> a = a. Moreover 1 \<noteq> 0. 

(The assertion that 1 \<noteq> 0 may seem a strange fact to list, but we have to list
it, because there is no way it could possibly be proved on the basis of the
other properties listed--these properties would all hold if there were 
only one number, namely, 0.)

  (P7) For every number a \<noteq> 0, there is a number a^{-1} such that

          a \<cdot> a^{-1} = a^{-1} \<cdot> b = 1.

  (P8) If a and b are numbers, then
           a \<cdot> b =  b \<cdot> a
*)
lemma mul_assoc: (* P5 *)
  fixes a::r and b::r and c::r
  shows "((a \<odot> b) \<odot> c) =  (a \<odot> (b \<odot> c))"
  sorry

(* EXERCISE 5: Write P6 (giving it the name 'mul_ident' as a lemma, using 
'sorry' as a proof; mimic the format of prior property-lemmas. Be
sure to include three separate conclusions in your "shows" line. Use the 
name "U" (for 'unit') instead of "1". *)
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

(* EXERCISE 6: mimic the proof above in Isabelle, using "reciprocal" as the 
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

lemma mulZ: 
  fixes a
  shows "(a  \<odot> Z) = Z" and "(Z  \<odot> a) = Z"
proof -
  have 0:"Z  \<oplus> Z = Z" using additive_ident by auto
  have 1: "a  \<odot> (Z \<oplus> Z) = (a  \<odot> Z)" using 0 by auto
  have 2: "(a  \<odot> Z) \<oplus> (a  \<odot> Z) = (a  \<odot> Z)" using 1 distrib by auto
  have 3: "((a  \<odot> Z) \<oplus> (a  \<odot> Z)) \<oplus> (neg (a  \<odot> Z))  = (a  \<odot> Z)  \<oplus> (neg (a  \<odot> Z))" 
    using 2 by auto
  have 4: "(a  \<odot> Z) \<oplus> ((a  \<odot> Z) \<oplus> (neg (a  \<odot> Z)))  = Z" 
    using 3 plus_assoc negation by auto
  have 5: "(a  \<odot> Z) \<oplus> (Z)  = Z" 
    using 4 negation by auto
  show 6:"(a  \<odot> Z)  = Z" 
    using 5 additive_ident by auto
  show 7:"(Z  \<odot> a)  = Z" using 6 mul_commute by auto
qed

lemma unique_neg:
  fixes a b
  assumes "u  \<oplus> x = Z"
  shows "x = neg u"
proof -
  have 0:  "u  \<oplus> x = Z" using assms by auto
  have 1: "(neg u)  \<oplus> (u  \<oplus> x) = (neg u)  \<oplus> Z" using 0 by auto
  have 2: "((neg u)  \<oplus> u)  \<oplus> x = (neg u)" 
    using 1 additive_ident plus_assoc by auto
  have 3: "Z  \<oplus> x = (neg u)" using 2 negation by auto
  thus ?thesis using additive_ident 3 by auto
qed


lemma negneg:
  fixes a::r 
  shows "neg (neg a) = a"
proof -
  have 0: "(neg a)  \<oplus> a = Z" using unique_neg negation by auto
  have 1: "neg (neg a) = a" using 0 unique_neg by auto
  show ?thesis using 1 by auto
qed

lemma move_neg: 
  fixes a b
  shows "(neg a)  \<odot> b = neg(a  \<odot> b)"
proof -
  have 0:"((neg a)  \<odot> b) \<oplus> (a  \<odot> b) = (b  \<odot> (neg a)) \<oplus> (b  \<odot> a)" using mul_commute by auto
  have 1:"((neg a)  \<odot> b) \<oplus> (a  \<odot> b) = (b  \<odot> ((neg a) \<oplus> a))" using 0 distrib by auto
  have 2:"((neg a)  \<odot> b) \<oplus> (a  \<odot> b) = (b  \<odot> Z)" using 1 negation by auto
  have 3:"((neg a)  \<odot> b) \<oplus> (a  \<odot> b) = Z" using 2 mulZ by auto
  have 4: " (a  \<odot> b) \<oplus> ((neg a)  \<odot> b) = Z" using 3 plus_commute by auto
  show ?thesis  using 4 unique_neg  by auto
qed

lemma neg_product: 
  fixes a b
  shows "(neg a)  \<odot> (neg b) = a  \<odot> b"
proof -
  have 0: "((neg a)  \<odot> (neg b)) \<oplus> neg(a  \<odot> b) = ((neg a)  \<odot> (neg b))  \<oplus> (neg(a)  \<odot> b)" 
    using move_neg by auto
  have 1: "((neg a)  \<odot> (neg b)) \<oplus> neg(a  \<odot> b) = ((neg a)  \<odot> ((neg b)  \<oplus>  b))" using 0 distrib by auto 
  have 2: "((neg a)  \<odot> (neg b)) \<oplus> neg(a  \<odot> b) = (neg a)  \<odot> Z" using 1 negation by auto 
  have 3: "((neg a)  \<odot> (neg b)) \<oplus> neg(a  \<odot> b) =  Z" using 2 mulZ by auto
  have 4: "(((neg a)  \<odot> (neg b)) \<oplus> neg(a  \<odot> b)) \<oplus> (a  \<odot> b) =  Z  \<oplus> (a  \<odot> b)" using 3 by auto
  have 5: "((neg a)  \<odot> (neg b)) \<oplus> (neg(a  \<odot> b) \<oplus> (a  \<odot> b)) =  (a  \<odot> b)" 
    using 4 plus_assoc additive_ident by auto
  have 6: "((neg a)  \<odot> (neg b)) \<oplus> Z =  (a  \<odot> b)" 
    using 5 negation by auto
  show ?thesis 
    using 6 additive_ident by auto
qed

(* A few more warmup lemmas about zero, negation, and subtraction *)

lemma negZ_is_Z:
  shows "neg Z = Z"
(*hint: Z + (neg Z) = Z; does a prior lemma then help? *)
proof -
  have 0: "Z  \<oplus> (neg Z) = Z" using negation by auto
  show ?thesis using 0 ex2 by auto
qed

lemma subtractZ_is_identity:
  shows "a \<ominus> Z = a"
proof -
  show ?thesis using diff_def negZ_is_Z additive_ident by auto
qed

(* Additional material to get you started on positive and negative
numbers *)
consts
P::"r set"

lemma trichotomy: (* Spivak's P10 *)
  fixes a
  shows "(a = Z \<and> \<not>( a \<in> P \<or>  (neg a) \<in> P)) \<or>
(a \<in> P \<and> \<not>( a = Z \<or>  (neg a) \<in> P)) \<or>
((neg a) \<in> P \<and> \<not>( a = Z \<or> a \<in> P))"
  sorry

lemma additive_closure: (*Spivak's P11 *)
  fixes a b
  assumes "a \<in> P" and "b \<in> P"
  shows "a \<oplus> b \<in> P"
  sorry

lemma multiplicative_closure: (*Spivak's P12 *)
  fixes a b
  assumes "a \<in> P" and "b \<in> P"
  shows "a \<odot> b \<in> P"
  sorry

definition gt::"r \<Rightarrow> r \<Rightarrow> bool"
  where "gt a b = ((a \<ominus> b)  \<in> P)" 
 
definition ge::"r \<Rightarrow> r \<Rightarrow> bool"
  where "ge a b = ((a \<ominus> b)  \<in> P \<or> a = b)" 

definition lt::"r \<Rightarrow> r \<Rightarrow> bool"
  where "lt a b = gt b a" 

definition le::"r \<Rightarrow> r \<Rightarrow> bool"
  where "le a b = ge b a" 

notation gt  (infix "gt" 20)
notation ge  (infix "ge" 20)
notation lt  (infix "lt" 20)
notation le  (infix "le" 20)

lemma gtP1:
  assumes "a gt Z"
  shows "a \<in> P"
proof -
  have 0:"a \<ominus> Z \<in> P" using assms(1) gt_def by simp
  show ?thesis using 0 subtractZ_is_identity  by auto
qed

lemma gtP2:
  assumes "a \<in> P"
  shows "a gt  Z"
proof -
  have 0:"a \<ominus> Z \<in> P" using assms(1) subtractZ_is_identity  by auto
  show ?thesis using 0 gt_def  by auto
qed

lemma gt_le:
  fixes a b
  assumes "a le b"
  shows "\<not> (a gt b)"
proof -
  show ?thesis using assms gt_def le_def ge_def diff_def trichotomy 
      plus_assoc unique_neg negation by metis
qed

lemma le_gt:
  fixes a b
  assumes "a gt b"
  shows "\<not> (a le b)"
proof -
  show ?thesis using assms gt_def le_def ge_def diff_def trichotomy 
      plus_assoc unique_neg negation by metis
qed

lemma lt_ge:
  fixes a b
  assumes "a lt b"
  shows "\<not> (a ge b)"
proof -
  show ?thesis using assms gt_def lt_def le_def ge_def diff_def trichotomy 
      plus_assoc unique_neg negation by metis
qed


lemma ge_lt:
  fixes a b
  assumes "a ge b"
  shows "\<not> (a lt b)"
proof -
  show ?thesis using assms gt_def lt_def le_def ge_def diff_def trichotomy 
      plus_assoc unique_neg negation by metis
qed

lemma trichotomy2: 
  fixes a b
  shows "(a \<ominus> b = Z \<and> \<not>( a \<ominus> b \<in> P \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( a \<ominus> b = Z \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
((neg (a \<ominus> b)) \<in> P \<and> \<not>( a \<ominus> b = Z \<or> a \<ominus> b \<in> P))"
proof -
  show ?thesis using trichotomy by auto
qed

lemma diff_zero_equals: 
  fixes a b
  assumes "a \<ominus> b = Z"
  shows "a = b"
proof -
  have 0:"a \<oplus> (neg b) = Z" using diff_def assms by auto
  have 1:"(a \<oplus> (neg b)) \<oplus>  b = Z  \<oplus>  b" using 0  by auto
  have 2:"a \<oplus> ((neg b)\<oplus>  b ) = Z  \<oplus>  b" using 1 plus_assoc by auto
  have 3:"a \<oplus> Z  = Z  \<oplus>  b" using 2 negation by auto
  show ?thesis using 3 additive_ident by auto
qed

lemma diff_positive_gt: 
  fixes a b
  assumes "a \<ominus> b \<in> P"
  shows "a gt b"
proof -
  show ?thesis using assms gt_def by auto
qed

lemma negsub:
  fixes a b
  shows "b \<ominus> a = neg(a \<ominus> b)"
proof -
  have 0: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = (b \<oplus> (neg a))  \<oplus> (a \<oplus> (neg b))"
    using diff_def by auto
  have 1: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = ((b \<oplus> (neg a))  \<oplus> a) \<oplus> (neg b)"
    using 0 plus_assoc by auto
  have 2: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = (b \<oplus> ((neg a)  \<oplus> a)) \<oplus> (neg b)"
    using 1 plus_assoc by auto
  have 3: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = (b \<oplus> Z) \<oplus> (neg b)"
    using 2 negation by auto
  have 4: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = (b ) \<oplus> (neg b)"
    using 3 additive_ident by auto
  have 5: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = Z"
    using 4 negation by auto
  have 6: "(a \<ominus> b)  \<oplus> (b \<ominus> a) = Z"
    using 5 plus_commute by auto
  show ?thesis using 6 unique_neg by auto
qed

lemma trich_help3: 
  fixes a b
  assumes "(neg (a \<ominus> b)) \<in> P"
  shows "b gt a"
proof -
  have 0: "neg(a \<ominus> b) = b \<ominus> a" using  negsub by metis
  have 1: "b \<ominus> a \<in> P" using assms 0 by auto
  show ?thesis using 1 gt_def by auto 
qed


lemma trich_help3b: 
  fixes a b
  assumes "b gt a"
  shows "(neg (a \<ominus> b)) \<in> P"
proof -
  have 0: "b \<ominus> a \<in> P" using assms gt_def by auto
  have 1: "neg(a \<ominus> b) = b \<ominus> a" using  negsub by metis
  have 2: "neg(a \<ominus> b) \<in> P" using 0 1  by auto
  show ?thesis using 2 gt_def by auto 
qed

lemma trich_help3c:
  fixes a b
  shows "(b gt  a) = ((neg (a \<ominus> b)) \<in> P)"
proof -
  show ?thesis using trich_help3 trich_help3b by auto
qed

lemma trichotomy3:
  fixes a b
  assumes "h1 = (a = b)" and "h2 = (a gt b)" and "h3 = (b gt a)"
  shows "(h1 \<and> \<not>( h2 \<or> h3)) \<or> 
        (h2 \<and> \<not>( h1 \<or> h3)) \<or> 
        (h3 \<and> \<not>( h1 \<or> h2))"
proof -
  have 0: "(a \<ominus> b = Z \<and> \<not>( a \<ominus> b \<in> P \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( a \<ominus> b = Z \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
((neg (a \<ominus> b)) \<in> P \<and> \<not>( a \<ominus> b = Z \<or> a \<ominus> b \<in> P))" using  trichotomy2 assms by auto
  have 1: "(a = b \<and> \<not>( a \<ominus> b \<in> P \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( a \<ominus> b = Z \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
((neg (a \<ominus> b)) \<in> P \<and> \<not>(  a \<ominus> b = Z \<or> a \<ominus> b \<in> P))" 
    using  0 diff_zero_equals by auto
  have 2: "(a = b \<and> \<not>( a \<ominus> b \<in> P \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( (a = b) \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
((neg (a \<ominus> b)) \<in> P \<and> \<not>(  (a = b) \<or> a \<ominus> b \<in> P))" 
    using  1 diff_zero_equals by (metis negsub)
  have 3: "(h1 \<and> \<not>( a \<ominus> b \<in> P \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( h1 \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
((neg (a \<ominus> b)) \<in> P \<and> \<not>( h1 \<or> a \<ominus> b \<in> P))" 
    using  2 assms(1) by auto
  have 4: " a \<ominus> b \<in> P = (a gt b)" using gt_def by auto
  have 5: "(h1 \<and> \<not>((a gt b) \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
( (a gt b) \<and> \<not>( h1 \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
((neg (a \<ominus> b)) \<in> P \<and> \<not>( h1 \<or> (a gt b)))" 
    using  3 4 by auto 
  have 6 :"(neg (a \<ominus> b) \<in> P) = h3" using trich_help3c assms by auto
  have 7 :"(h1 \<and> \<not>((a gt  b) \<or> h3)) \<or>
((a gt  b) \<and> \<not>( h1 \<or>  h3)) \<or>
(h3 \<and> \<not>( h1 \<or> (a gt b)))"  using 5 6 by auto
  show ?thesis using 7 assms gt_def by auto
qed

lemma neg_sum:
  fixes a b
  shows "neg (a  \<oplus> c) = (neg a)  \<oplus> (neg c)"
proof -
  have 0: "(a  \<oplus> c) \<oplus> ( (neg a)  \<oplus> (neg c)) = Z" 
  proof -
    have 1: "(a  \<oplus> c) \<oplus> ( (neg a)  \<oplus> (neg c)) = ((a  \<oplus> c) \<oplus>  (neg a))  \<oplus> (neg c)"
      using plus_assoc  by auto
    have 2: "(a  \<oplus> c) \<oplus> ( (neg a)  \<oplus> (neg c)) = (a  \<oplus> (c \<oplus>  (neg a)))  \<oplus> (neg c)"
      using plus_assoc 1  by auto
    have 3: "(a  \<oplus> c) \<oplus> ( (neg a)  \<oplus> (neg c)) = (a  \<oplus> ((neg a) \<oplus> c))  \<oplus> (neg c)"
      using plus_commute 2  by auto
    have 4: "(a  \<oplus> c) \<oplus> ( (neg a)  \<oplus> (neg c)) = ((a  \<oplus> (neg a)) \<oplus> c)  \<oplus> (neg c)"
      using plus_assoc 3  by auto
    have 5: "(a  \<oplus> c) \<oplus> ( (neg a)  \<oplus> (neg c)) = (Z \<oplus> c)  \<oplus> (neg c)"
      using  negation 4  by auto
    have 6: "(a  \<oplus> c) \<oplus> ( (neg a)  \<oplus> (neg c)) = Z \<oplus> (c  \<oplus> (neg c))"
      using  plus_assoc 5  by auto
    have 7: "(a  \<oplus> c) \<oplus> ( (neg a)  \<oplus> (neg c)) = Z \<oplus> Z"
      using  negation 6  by auto
    show ?thesis
      using  additive_ident 7  by auto
  qed
  show ?thesis using 0 unique_neg by auto 
qed

lemma lt_add_const:
  fixes a b c
  assumes "a lt b"
  shows  "(a  \<oplus> c) lt (b  \<oplus> c)"
proof -
  have 0:"(b  \<ominus> a) \<in> P" using assms lt_def gt_def by auto
  have 1: "b  \<oplus> (neg a) \<in> P" using 0 diff_def by auto
  have 2: "(b  \<oplus> (neg a))  \<oplus> (c  \<oplus> (neg c)) \<in> P" 
    using 1 negation additive_ident by auto
  have 3: "((b  \<oplus> (neg a))  \<oplus> c)  \<oplus> (neg c) \<in> P" 
    using  2 plus_assoc by auto
  have 4: "(b  \<oplus> ((neg a)  \<oplus> c))  \<oplus> (neg c) \<in> P" 
    using  3 plus_assoc by auto
  have 5: "(b  \<oplus> (c  \<oplus> (neg a)))  \<oplus> (neg c) \<in> P" 
    using 4 plus_commute by auto
  have 6: "((b  \<oplus> c)  \<oplus> (neg a))  \<oplus> (neg c) \<in> P" 
    using 5 plus_assoc by auto
  have 7: "(b  \<oplus> c)  \<oplus> ((neg a)  \<oplus> (neg c)) \<in> P" 
    using 6 plus_assoc by auto
  have 8: "(b  \<oplus> c)  \<oplus> (neg (a  \<oplus> c)) \<in> P" 
    using 7 neg_sum by auto
  have 9: "(b  \<oplus> c)  \<ominus>  (a  \<oplus> c)   \<in> P" 
    using 8 diff_def by auto
  show ?thesis using diff_def 9 lt_def gt_def by auto
qed

lemma lt_transitive: 
  fixes a b c
  assumes "a lt b" and "b lt c"
  shows "a lt c"
proof -
  have 0:"(b  \<ominus> a) \<in> P" using assms(1) lt_def gt_def by auto
  have 1:"(c  \<ominus> b) \<in> P" using assms(2) lt_def gt_def by auto
  have 2:"(c  \<ominus> b)  \<oplus> (b  \<ominus> a) \<in> P" using 0 1 additive_closure by auto
  have 3:"(c  \<oplus> (neg b))  \<oplus> (b   \<oplus> (neg a)) \<in> P" using 2 diff_def by auto
  have 4:"c  \<oplus> ((neg b)  \<oplus> (b   \<oplus> (neg a))) \<in> P" using 3 plus_assoc by auto
  have 5:"c  \<oplus> (((neg b)  \<oplus> b)   \<oplus> (neg a)) \<in> P" using 4 plus_assoc by auto
  have 6:"c  \<oplus> (Z   \<oplus> (neg a)) \<in> P" using 5 negation by auto
  have 7:"c  \<oplus> (neg a) \<in> P" using 6 additive_ident by auto
  have 8:"(c  \<ominus> a) \<in> P" using 7 diff_def by auto
  show ?thesis using 8 lt_def gt_def by auto
qed

definition NN where "NN = P \<union> {Z}"

lemma NN_sum_closure:
  fixes a b
  assumes "a \<in>  NN"
  assumes "b \<in>  NN"
  assumes "b \<in>  NN"
  shows "a  \<oplus> b  \<in>  NN"
proof (cases "a = Z")
  case True
  have 0: "a  \<oplus> b = b" using True additive_ident by auto
  have 1: "b  \<in>  NN" using assms by auto
  then show ?thesis using 0 1 by auto
next
  case False
  have aPos: "a \<in> P" using False NN_def assms 
    by auto
  then show ?thesis 
  proof (cases "b = Z")
    case True
    have 1: "a  \<oplus> b = a"  using True additive_ident by auto
    have 2: "a  \<oplus> b \<in> P" using 1 aPos by auto
    then show ?thesis using 2 assms NN_def by auto
  next
    case False
    have 3:"b \<in> P" using NN_def assms False by auto
    have 4: "a  \<oplus> b \<in> P" using 3 aPos additive_closure by auto
    then show ?thesis using 4 assms NN_def by auto
  qed

qed

lemma NN_ge:
  fixes a b
  assumes "a ge b"
  shows "a  \<ominus> b  \<in>  NN"
proof -
  have 00:"a ge b" using assms(1) le_def by auto  
  have 01:"(a  \<ominus> b) \<in> P \<or> a = b" using 00  ge_def by auto 
  have 02:"(a  \<ominus> b) \<in> P \<or> (a  \<ominus> b) \<in>  {Z}" using 01 diff_def negation negZ_is_Z by auto 
  have 0:"(a \<ominus> b) \<in> NN" using 02 NN_def by auto
  then show ?thesis by auto
qed

lemma ge_NN:
  fixes a b
  assumes "a  \<ominus> b  \<in>  NN"
  shows "a ge b"
proof -
  have 01:"a  \<ominus> b  \<in>  NN" using assms(1) by auto
  have 02:"(a  \<ominus> b) \<in> P \<or> (a  \<ominus> b) = Z" using 01 NN_def by auto 
  have 03:"(a  \<ominus> b) \<in> P \<or> (a \<oplus> neg b) = Z" using 02  diff_def negation by auto
  have 04:"(a  \<ominus> b) \<in> P \<or> (a \<oplus> neg b)\<oplus> b = Z\<oplus> b" using 03  by auto
  have 05:"(a  \<ominus> b) \<in> P \<or> (a \<oplus> (neg b\<oplus> b)) = Z\<oplus> b" using 04 plus_assoc  by auto
  have 06:"(a  \<ominus> b) \<in> P \<or> (a \<oplus> Z) = b" using 05 additive_ident negation  by auto
  have 06:"(a  \<ominus> b) \<in> P \<or> a = b" using 06 additive_ident by auto
  have 00:"a ge b" using 06 ge_def by auto  
  then show ?thesis by auto
qed

lemma ge_or_lt:
  fixes a b
  shows "(a ge b) \<or> (a lt b)"
proof -
  show ?thesis 
    using ge_def gt_def lt_def trichotomy3 by blast
qed


lemma le_transitive: 
  fixes a b c
  assumes "a le  b" and "b le  c"
  shows "a le  c"
proof -
 
  have 00:"b ge a" using assms(1) le_def by auto  
  have 0:"(b \<ominus> a) \<in> NN" using 00 NN_ge by auto

  have 10:"c ge b" using assms(2) le_def by auto  
  have 1:"(c  \<ominus> b) \<in> NN" using 10 NN_ge by auto
  have 2:"(c  \<ominus> b)  \<oplus> (b  \<ominus> a) \<in> NN" using 0 1 additive_closure NN_def 
    using NN_sum_closure by auto
  have 3:"(c  \<oplus> (neg b))  \<oplus> (b   \<oplus> (neg a)) \<in> NN" using 2 diff_def by auto
  have 4:"c  \<oplus> ((neg b)  \<oplus> (b   \<oplus> (neg a))) \<in> NN" using 3 plus_assoc by auto
  have 5:"c  \<oplus> (((neg b)  \<oplus> b)   \<oplus> (neg a)) \<in> NN" using 4 plus_assoc by auto
  have 6:"c  \<oplus> (Z   \<oplus> (neg a)) \<in> NN" using 5 negation by auto
  have 7:"c  \<oplus> (neg a) \<in> NN" using 6 additive_ident by auto
  have 8:"(c  \<ominus> a) \<in> NN" using 7 diff_def by auto
  have 9: "c ge  a" using 8 ge_NN by auto
  have 10: "a le  c" using 9 le_def by simp
  then show ?thesis by auto
qed

lemma neg_prod_pos:
  fixes a b
  assumes "a lt Z" and "b lt Z"
  shows " (a  \<odot> b) gt Z"
proof -
  have 0: "Z gt  a" using assms lt_def by auto
  have 1: "Z gt  b" using assms lt_def by auto

  have 2: "Z  \<ominus>  a \<in> P" using 0 gt_def by auto
  have 3: "Z  \<ominus>  b \<in> P" using 1 gt_def by auto
  have 4: "neg a \<in> P" using 2 diff_def additive_ident by auto
  have 5: "neg b \<in> P" using 3 diff_def additive_ident by auto
  have 6: "(neg a  \<odot>  neg b) \<in> P" 
    using 4 5 multiplicative_closure  by auto
  have 7:  "(a  \<odot>  b) \<in> P" using 6 neg_product by auto
  have 8:  "(a  \<odot>  b) \<oplus> Z \<in> P" using 7 additive_ident by auto
  have 9:  "(a  \<odot>  b) \<oplus> (neg Z) \<in> P" using 8 negZ_is_Z by auto
  have 10:  "(a  \<odot>  b)  \<ominus>  Z \<in> P" using 9 diff_def by auto
  show ?thesis using 10 gt_def by auto 
qed

lemma square_pos:
  fixes b
  assumes "b \<noteq> Z"
  shows " (b \<odot> b) gt  Z"
proof -
  have 0: "b \<in> P \<or> (neg b) \<in> P" using assms trichotomy by auto
  show ?thesis
  proof (cases "b \<in> P")
    case True
    have "(b \<odot> b) \<in> P" using True multiplicative_closure by auto
    hence "(b \<odot> b)  \<oplus> Z  \<in> P" using additive_ident by auto
    hence "(b \<odot> b)  \<oplus> (neg Z)  \<in> P" using negZ_is_Z  by auto
    hence "(b \<odot> b)  \<ominus>  Z  \<in> P" using diff_def  by auto
    
    then show ?thesis using gt_def by auto
  next
    case False
    have "(neg b) \<in> P" using 0 False by auto
    hence "b lt Z" using lt_def gt_def 
      by (simp add: additive_ident(2) diff_def)
    then show ?thesis using neg_prod_pos by auto 
  qed
qed

lemma one_pos:
  shows "U gt  Z"
proof -
  have "U \<noteq> Z" using mul_ident by simp
  hence  "(U \<odot> U) gt Z" using square_pos by auto
  then show ?thesis using mul_ident by auto
qed


definition abs  where
"abs a  \<equiv> (if (a ge Z) then a else neg a)"

(* Tiny lemmas *)
lemma nnabs:
  fixes a::r
  assumes "a ge Z"
  shows "(abs a) = a"
proof -
  show ?thesis using assms abs_def by auto
qed

lemma gt_weaken:
  fixes a::r
  assumes "a gt Z"
  shows "a ge Z"
proof -
  show ?thesis using assms gt_def ge_def by auto
qed

lemma ge_ne:
  fixes a::r
  assumes "a ge b" and "a \<noteq> b"
  shows "a gt b"
proof -
  show ?thesis using assms gt_def ge_def by auto
qed

lemma le_ne:
  fixes a::r
  assumes "a le b" and "a \<noteq> b"
  shows "a lt b"
proof -
  show ?thesis using assms lt_def le_def gt_def ge_def by auto
qed

lemma le_sum_const:
  fixes a b c
  assumes "a le b" 
  shows "(a \<oplus> c) le (b \<oplus> c)"
proof -
  have 1: "b ge a" using assms le_def by auto
  have 2: "(b  \<ominus> a) \<in> P \<or> b = a" using ge_def 1 by auto
  show ?thesis
  proof (cases "b = a")
    case True
    have 1: "b  \<oplus> c = a  \<oplus> c" using True assms by auto 
    then show ?thesis using le_def 1 ge_def by auto
  next
    case False
    have 1: "(b  \<ominus> a) \<in> P" using 2 False by auto
    have 2: "b  \<oplus> (neg a) \<in> P" using 1 diff_def by auto
    have 3: "c  \<oplus> (neg c) = Z" using negation by auto
    have 4: "(b  \<oplus> (neg a)) \<oplus> (c  \<oplus> neg c) = (b  \<oplus> (neg a))" using additive_ident 3 by auto
    have 5: "(b  \<oplus> (neg a)) \<oplus> (c  \<oplus> neg c) \<in> P" using 2 4 by auto
    have 6: "((b  \<oplus> (neg a)) \<oplus> c)  \<oplus> (neg c) \<in> P" using 5 plus_assoc by auto
    have 7: "(b  \<oplus> ((neg a) \<oplus> c))  \<oplus> (neg c) \<in> P" using 6 plus_assoc by auto
    have 8: "(b  \<oplus> (c \<oplus> (neg a)))  \<oplus> (neg c) \<in> P" using 7 plus_commute [of "c" "neg a"] by auto
    have 9: "((b  \<oplus> c) \<oplus> (neg a))  \<oplus> (neg c) \<in> P" using 8 plus_assoc by auto
    have 10: "(b  \<oplus> c) \<oplus> ((neg a)  \<oplus> (neg c)) \<in> P" using 9 plus_assoc by auto
    have 11: "(b  \<oplus> c) \<oplus> (neg (a  \<oplus> c)) \<in> P" using 10 neg_sum by auto
    have 12: "(b  \<oplus> c) \<ominus>  (a  \<oplus> c) \<in> P" using 11 diff_def by auto
    then show ?thesis using le_def ge_def 12 by auto
  qed
qed

lemma le_sum:
  fixes a b c d
  assumes "a le c" and "b le d"
  shows "(a \<oplus> b) le (c \<oplus> d)"
proof -
  have 1: "(a \<oplus> b) le (c \<oplus> b)" using assms(1)  le_sum_const by auto
  have 2: "(b \<oplus> c) le (d \<oplus> c)" using assms(2)  le_sum_const by auto
  have 3: "(c \<oplus> b) le (c \<oplus> d)" using 2 plus_commute by auto
  show ?thesis using 1 3 le_transitive by auto
qed

lemma equals_add_equals: 
  fixes a::r and b and c
  assumes "a = b"
  shows "a \<oplus> c = b \<oplus> c"
proof -
  show ?thesis using assms HOL.arg_cong by auto
qed

lemma self_diff:
  fixes a::r 
  shows "a \<ominus> a = Z"
proof -
  have 1: "a \<ominus> a = a \<oplus> (neg a)" using diff_def by auto
  have 2: "a \<oplus> (neg a) = Z" using negation 1 by auto
  show ?thesis using 1 2 by auto
qed

lemma lt_not_eq_h:
  fixes a::r and b
  assumes "a lt b" and "a = b"
  shows "False"
proof - 
  have 1: "b gt a" using assms lt_def by auto
  have 2: "b \<ominus> a \<in> P" using gt_def 1 by auto
  have 3: "b \<ominus> b \<in> P" using 2 assms by auto
  have 4: "Z  \<in> P" using 3 self_diff by auto
  show ?thesis  using trichotomy 4 by auto
qed

lemma lt_not_eq:
  fixes a::r and b
  assumes "a lt b" 
  shows "a \<noteq>  b"
proof - 
  show ?thesis using assms lt_not_eq_h by auto
qed

lemma lt_not_ge:
  fixes a::r and b
  assumes "a lt b"
  shows "\<not>( a ge b)"
proof - 
  show ?thesis using assms lt_ge by auto
qed

lemma posneg:
  fixes a::r
  assumes "a gt Z"
  shows "(neg a) lt Z"
proof -
  have 1: "a \<ominus> Z \<in> P" using assms gt_def by auto
  also have 2: "a \<ominus> Z = a" using subtractZ_is_identity by auto
  have 3: "a \<in> P" using 1 2 by auto
  have 4: "Z \<oplus> a \<in> P" using additive_ident 3 by auto
  have 5: "Z  \<oplus> (neg (neg a)) \<in> P" using negneg 4 by auto
  have 6: "Z \<ominus> (neg a) \<in> P" using 5 diff_def by auto
  have 7: "Z gt (neg a)" using 6 gt_def by auto
  show ?thesis using 7 lt_def by auto
qed

lemma negpos:
  fixes a::r
  assumes "a lt Z"
  shows "(neg a) gt Z"
proof -
  have 1: "Z \<ominus> a \<in> P" using assms lt_def gt_def by auto
  have 4: "Z \<oplus> (neg a) \<in> P" using diff_def 1 by auto
  have 5: " (neg a) \<in> P" using additive_ident 4  by auto
  have 6: " (neg a) \<ominus> Z \<in> P" using subtractZ_is_identity 5  by auto
  thus ?thesis using gt_def by auto
qed

(* ==== a long-winded triangle-ineq proof*)
lemma ti_z:
  fixes a
  assumes "a = Z"
  shows "(abs ( neg a)) =  (abs a)"
proof -
  have 1: "a ge Z" using assms ge_def gt_def by auto
  have 2: "abs a = a" using abs_def 1 by auto
  have 3: "neg a = Z" using negZ_is_Z assms by auto
  have 4: "neg a ge Z" using ge_def 3 by auto
  have 5: "abs (neg a) = neg a" using 4 abs_def by auto
  have 6: "abs (neg a) = a" using 3 assms 5 by auto
  thus ?thesis using 6 2 by auto
qed

lemma abs_zero:
  shows "abs Z = Z"
proof -
  show ?thesis using abs_def negZ_is_Z by auto
qed

lemma abs_pos:
  fixes a
  assumes "a \<in> P"
  shows "(abs a) = a"
proof -
  show ?thesis using assms abs_def ge_def subtractZ_is_identity by auto
qed

lemma abs_NN:
  fixes a
  assumes "a ge Z"
  shows "(abs a) = a"
proof (cases "a = Z")
  case True
  then show ?thesis using True abs_zero by auto
next
  case False
  have 1: "(a \<ominus> Z \<in> P \<or> a = Z)" using ge_def assms by auto
  have 2: "(a \<ominus> Z \<in> P)" using 1 False by auto
  have 3: "a  \<in> P" using 2 subtractZ_is_identity by auto
  show ?thesis using 3 abs_pos by auto
qed


lemma abs_neg:
  fixes a
  assumes "\<not> (a \<in> P)" and "\<not> (a = Z)" 
  shows "(abs a) = neg a"
proof -
  show ?thesis using assms abs_def ge_def subtractZ_is_identity negZ_is_Z by auto
qed

lemma abs_neg2:
  fixes a
  assumes "a le Z" 
  shows "(abs a) = neg a"
proof (cases "a = Z")
  case True
  then show ?thesis using abs_zero True assms le_def ge_def negZ_is_Z by auto
next
  case False
  have 1:  "Z  \<ominus>  a  \<in> P" using assms le_def ge_def False  by auto
  have 2:  "Z   \<oplus> neg a  \<in> P" using 1 diff_def   by auto
  have 3: "neg a \<in> P" using 2 additive_ident by auto
  have 4:  "\<not> (a \<in> P)" and "\<not> (a = Z)" using 3 trichotomy by auto
  then show ?thesis using abs_neg by auto
qed

lemma ti_x1:
  fixes a
  assumes "a gt Z"
  shows "(abs ( neg a)) =  (abs a)"
proof -
  show ?thesis
    using abs_NN abs_neg assms gt_weaken negneg trichotomy by metis
qed

lemma ti_x2:
  fixes a
  assumes "a lt Z"
  shows "(abs ( neg a)) =  (abs a)"
proof - 
  have 1: "Z gt a" using assms lt_def by auto
  have 2: "Z  \<ominus>  a  \<in> P" using 1 gt_def by auto
  have 3: "Z  \<oplus> neg a  \<in> P" using 2 diff_def by auto
  have 5: "neg a  \<in> P" using 3 additive_ident by auto
  have 6: "neg a gt Z" using 5 gt_def subtractZ_is_identity by auto
  thus ?thesis using 6 ti_x1 [of "(neg a)"] negneg by auto
qed

lemma tix3:
  fixes a
  shows "(abs ( neg a)) =  (abs a)"
proof -
  have 1: "(a lt Z) \<or> (a = Z) \<or> (a gt Z)" using lt_def gt_def diff_def trichotomy3 by fastforce
  show ?thesis using 1 ti_z ti_x1 ti_x2 negZ_is_Z by auto
qed

lemma ti_y1:
  fixes a
  shows "a le (abs a)"
proof (cases "a ge Z")
  case True
  then show ?thesis    using abs_def ge_def le_def by simp
next
  case False
  then show ?thesis
    using abs_def additive_closure diff_def ge_def le_def subtractZ_is_identity trichotomy by metis
qed


lemma ti_lhsNN:
  fixes a and b
  assumes "(a \<oplus> b) ge Z"
  shows "(abs (a \<oplus> b)) le  ((abs a)  \<oplus> (abs b))"
proof -
  have 1: "(abs (a \<oplus> b)) = (a \<oplus> b)" using assms abs_NN   by auto
  have 2: "a le (abs a)" using ti_y1 by auto
  have 3: "b le (abs b)" using ti_y1 by auto
  have 4: " (a \<oplus> b) le  ((abs a) \<oplus> (abs b))" using le_sum 2 3 by auto
  show ?thesis using 1 4 le_transitive by auto
qed

lemma ti_lhs_negative:
  fixes a and b
  assumes "(a \<oplus> b) lt Z"
  shows "(abs (a \<oplus> b)) le  ((abs a)  \<oplus> (abs b))"
proof -
  have 1: "abs (a \<oplus> b) = abs (neg (a \<oplus> b))" using assms tix3 by auto
  have 2: "neg (a \<oplus> b) ge Z" using assms negpos gt_weaken by auto
  have 3: "neg (a \<oplus> b) = (neg a) \<oplus> (neg b)" using neg_sum by auto
  have 4: "(neg a) \<oplus> (neg b) ge Z" using 2 3 by auto 
  have 5: "abs((neg a) \<oplus> (neg b)) le (abs(neg a) \<oplus> abs(neg b))" using 4 ti_lhsNN  by auto 
  have 6: "abs((neg a) \<oplus> (neg b)) le (abs(a) \<oplus> abs(b))" using 5 tix3  by auto 
  have 7: "abs( a \<oplus>  b) le (abs(a) \<oplus> abs(b))" using 1 5 6 3  by auto 
  show ?thesis using 7 by auto
qed

theorem triangle_inequality:   
  fixes a and b
  shows "(abs (a \<oplus> b)) le  ((abs a)  \<oplus> (abs b))"
proof -
  show ?thesis  using ge_or_lt ti_lhsNN ti_lhs_negative by blast
qed
