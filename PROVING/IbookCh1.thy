theory IbookCh1
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
negative::"r \<Rightarrow> r"
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
lemma plus_ident: (* Spivak calls this P2 *)
  fixes a::r
  shows "a \<oplus> Z =  a" and "Z \<oplus> a =  a"
  sorry

(* jfh: this is a case where I've put two conclusions in one "shows",
because I wanted to match Spivak's naming scheme. It may be easier for 
you to prove this as two separate lemmas, and then make the proof
of this lemma be "using negation_1 negation_2 by auto" *)

(* 
An important role is also played by 0 in the third property of our list:
*)
lemma negation: (* Spivak calls this P3 *)
  fixes a::r
  shows "a \<oplus> (negative a) =  Z"
  and  "(negative a) \<oplus> a =  Z"
  sorry

(* ================================
The remainder of this document is mostly duplicated in Ch1-Exercises.thy, where you, the
reader, are asked to fill in various lemmas and proofs. What's left here is my own 
version of that work, which you can look at if you become deeply frustrated by doing 
those exercises. You should switch to that file and start working through these 
exercises for yourself. 
==================================== *)


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
  have 0: "(negative a) \<oplus> (a \<oplus> x) = ((negative a) \<oplus> a)" using assms by auto
  have 1: "(negative a) \<oplus> (a \<oplus> x) = Z"  using 0 negation by auto
  have 2: "((negative a)\<oplus> a) \<oplus> x = Z" using 1 plus_assoc by auto
  have 3: "Z \<oplus> x = Z" using 2 negation by auto
  show ?thesis using 3 plus_ident by auto
qed

(* As we have just hinted, it is convenient to regard 
subtraction as an operation derived from addition; we consider
a - b to be an abbreviation for a + (-b). 
*)

definition diff:: "r \<Rightarrow> r \<Rightarrow> r" where
"diff a b \<equiv> (a \<oplus> (negative b))"

notation diff (infix "\<ominus>" 80) 
(* jfh: when you define diff like this, a new 'fact' is introduced on your
behalf, called "diff_def". There isn't a "negative_def" because we didn't actaully give
a definition of negation -- we just asserted a few properties that it has. So we have to cite
THOSE, rather than the definition, when we need them. We'll also define less-than, greater-than-
or-equal, etc. a bit later, and often use "lt_def", for example, in the course of a proof. 
*)
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
become convinced that they can always be supplied. In practice, it is
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
  have 1: "(x \<oplus> a) \<oplus> (negative a) = b \<oplus> (negative a)" using 0 by auto
  have 2: "(x \<oplus> a) \<oplus> (negative a) = x \<oplus> (a \<oplus> (negative a))" using plus_assoc by auto
  have 3: "x \<oplus> (a \<oplus> (negative a)) = b \<oplus> (negative a)" using 1 2 by auto
  have 4: "x \<oplus> Z = b \<oplus> (negative a)" using 3 negation(1) by auto
  have 5: "x = b \<oplus> (negative a)" using 4 plus_ident(1) by auto
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
from conventional mathematical practice. They actually DO define the 
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
  assumes "a \<odot> b = a \<odot> c" and "a \<noteq> Z"
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
  have 0: "Z \<oplus> Z = Z" using plus_ident by auto
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

(* jfh: there are a bunch more properties that I found myself using (and proving!)
more than once in subsequent parts of this document, so I separated them out
into lemmas, things like  x * 0 = 0 and 0 * x = 0, and -(-x) = x, and if 
x + y = 0, then y = -x (i.e., there's only one thing which, when added to
x gives us zero; our 'axiom" says that there's at least one, called "negative x", 
but this lemma shows it's unique). Also:
(-a) * b = -(a*b)
(-a) * (-b) = a*b
-0 = 0
a - 0 = a + (-0)
a - 0 = a + 0
a - 0 = a

*)

lemma mulZ: 
  fixes a
  shows "(a  \<odot> Z) = Z" and "(Z  \<odot> a) = Z"
proof -
  have 0:"Z  \<oplus> Z = Z" using plus_ident by auto
  have 1: "a  \<odot> (Z \<oplus> Z) = (a  \<odot> Z)" using 0 by auto
  have 2: "(a  \<odot> Z) \<oplus> (a  \<odot> Z) = (a  \<odot> Z)" using 1 distrib by auto
  have 3: "((a  \<odot> Z) \<oplus> (a  \<odot> Z)) \<oplus> (negative (a  \<odot> Z))  = (a  \<odot> Z)  \<oplus> (negative (a  \<odot> Z))" 
    using 2 by auto
  have 4: "(a  \<odot> Z) \<oplus> ((a  \<odot> Z) \<oplus> (negative (a  \<odot> Z)))  = Z" 
    using 3 plus_assoc negation by auto
  have 5: "(a  \<odot> Z) \<oplus> (Z)  = Z" 
    using 4 negation by auto
  show 6:"(a  \<odot> Z)  = Z" 
    using 5 plus_ident by auto
  show 7:"(Z  \<odot> a)  = Z" using 6 mul_commute by auto
qed

lemma unique_negative:
  fixes a b
  assumes "u  \<oplus> x = Z"
  shows "x = negative u"
proof -
  have 0:  "u  \<oplus> x = Z" using assms by auto
  have 1: "(negative u)  \<oplus> (u  \<oplus> x) = (negative u)  \<oplus> Z" using 0 by auto
  have 2: "((negative u)  \<oplus> u)  \<oplus> x = (negative u)" 
    using 1 plus_ident plus_assoc by auto
  have 3: "Z  \<oplus> x = (negative u)" using 2 negation by auto
  thus ?thesis using plus_ident 3 by auto
qed

lemma move_negative: 
  fixes a b
  shows "(negative a)  \<odot> b = negative (a  \<odot> b)"
proof -
  have 0:"((negative a)  \<odot> b) \<oplus> (a  \<odot> b) = (b  \<odot> (negative a)) \<oplus> (b  \<odot> a)" using mul_commute by auto
  have 1:"((negative a)  \<odot> b) \<oplus> (a  \<odot> b) = (b  \<odot> ((negative a) \<oplus> a))" using 0 distrib by auto
  have 2:"((negative a)  \<odot> b) \<oplus> (a  \<odot> b) = (b  \<odot> Z)" using 1 negation by auto
  have 3:"((negative a)  \<odot> b) \<oplus> (a  \<odot> b) = Z" using 2 mulZ by auto
  have 4: " (a  \<odot> b) \<oplus> ((negative a)  \<odot> b) = Z" using 3 plus_commute by auto
  show ?thesis  using 4 unique_negative  by auto
qed

lemma negative_product: 
  fixes a b
  shows "(negative a)  \<odot> (negative b) = a  \<odot> b"
proof -
  have 0: "((negative a)  \<odot> (negative b)) \<oplus> negative (a  \<odot> b) = ((negative a)  \<odot> (negative b))  \<oplus> (negative (a)  \<odot> b)" 
    using move_negative by auto
  have 1: "((negative a)  \<odot> (negative b)) \<oplus> negative (a  \<odot> b) = ((negative a)  \<odot> ((negative b)  \<oplus>  b))" using 0 distrib by auto 
  have 2: "((negative a)  \<odot> (negative b)) \<oplus> negative (a  \<odot> b) = (negative a)  \<odot> Z" using 1 negation by auto 
  have 3: "((negative a)  \<odot> (negative b)) \<oplus> negative (a  \<odot> b) =  Z" using 2 mulZ by auto
  have 4: "(((negative a)  \<odot> (negative b)) \<oplus> negative (a  \<odot> b)) \<oplus> (a  \<odot> b) =  Z  \<oplus> (a  \<odot> b)" using 3 by auto
  have 5: "((negative a)  \<odot> (negative b)) \<oplus> (negative (a  \<odot> b) \<oplus> (a  \<odot> b)) =  (a  \<odot> b)" 
    using 4 plus_assoc plus_ident by auto
  have 6: "((negative a)  \<odot> (negative b)) \<oplus> Z =  (a  \<odot> b)" 
    using 5 negation by auto
  show ?thesis 
    using 6 plus_ident by auto
qed

(* A few more warmup lemmas *)

lemma negZ:
  shows "negative Z = Z"
(*hint: Z + (negative Z) = Z; does a prior lemma then help? *)
proof -
  have 0: "Z  \<oplus> (negative Z) = Z" using negation by auto
  show ?thesis using 0 ex2 by auto
qed

lemma subtractZ:
  shows "a \<ominus> Z = a  \<oplus> (negative Z)"
proof -
  show ?thesis using diff_def by auto
qed

lemma subtractZ2:
  shows "a \<ominus> Z = a  \<oplus> Z"
proof -
  show ?thesis using subtractZ negZ by auto
qed

lemma subtractZ3:
  shows "a \<ominus> Z = a"
proof -
  show ?thesis using subtractZ2 plus_ident by auto
qed

(* Additional material to get you started on positive and negative
numbers *)
consts
P::"r set"

lemma trichotomy: (* Spivak's P10 *)
  fixes a
  shows "(a = Z \<and> \<not>( a \<in> P \<or>  (negative a) \<in> P)) \<or>
(a \<in> P \<and> \<not>( a = Z \<or>  (negative a) \<in> P)) \<or>
((negative a) \<in> P \<and> \<not>( a = Z \<or> a \<in> P))"
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

(* I've defined greater-than, greater-than-or-equal, less-than, less-than-or-equal, but
I didn't make 'infix' notation for them; on reflection perhaps I should have. 
Regardless, I rapidly found myself wanting to say things like a > 0 means a is in the set P, 
and NOT(a > 0) is the same as (a \<le> 0). So there are a bunch of lemmas to help out. 
You get to prove them all. *)

definition gt::"r \<Rightarrow> r \<Rightarrow> bool"
  where "gt a b = ((a \<ominus> b)  \<in> P)" 
 
definition ge::"r \<Rightarrow> r \<Rightarrow> bool"
  where "ge a b = ((a \<ominus> b)  \<in> P \<or> a = b)" 

definition lt::"r \<Rightarrow> r \<Rightarrow> bool"
  where "lt a b = gt b a" 

definition le::"r \<Rightarrow> r \<Rightarrow> bool"
  where "le a b = ge b a" 
 
lemma gtP1:
  assumes "gt a Z"
  shows "a \<in> P"
proof -
  have 0:"a \<ominus> Z \<in> P" using assms(1) gt_def by simp
  show ?thesis using 0 subtractZ3  by auto
qed

lemma gtP2:
  assumes "a \<in> P"
  shows "gt a Z"
proof -
  have 0:"a \<ominus> Z \<in> P" using assms(1) subtractZ3  by auto
  show ?thesis using 0 gt_def  by auto
qed

lemma trichotomy2: 
  fixes a b
  shows "(a \<ominus> b = Z \<and> \<not>( a \<ominus> b \<in> P \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( a \<ominus> b = Z \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
((negative (a \<ominus> b)) \<in> P \<and> \<not>( a \<ominus> b = Z \<or> a \<ominus> b \<in> P))"
proof -
  show ?thesis using trichotomy by auto
qed

lemma help1: 
  fixes a b
  assumes "a \<ominus> b = Z"
  shows "a = b"
proof -
  have 0:"a \<oplus> (negative b) = Z" using diff_def assms by auto
  have 1:"(a \<oplus> (negative b)) \<oplus>  b = Z  \<oplus>  b" using 0  by auto
  have 2:"a \<oplus> ((negative b)\<oplus>  b ) = Z  \<oplus>  b" using 1 plus_assoc by auto
  have 3:"a \<oplus> Z  = Z  \<oplus>  b" using 2 negation by auto
  show ?thesis using 3 plus_ident by auto
qed

lemma help2: 
  fixes a b
  assumes "a \<ominus> b \<in> P"
  shows "gt a b"
proof -
  show ?thesis using assms gt_def by auto
qed

lemma negsub:
  fixes a b
  shows "b \<ominus> a = negative (a \<ominus> b)"
proof -
  have 0: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = (b \<oplus> (negative a))  \<oplus> (a \<oplus> (negative b))"
    using diff_def by auto
  have 1: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = ((b \<oplus> (negative a))  \<oplus> a) \<oplus> (negative b)"
    using 0 plus_assoc by auto
  have 2: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = (b \<oplus> ((negative a)  \<oplus> a)) \<oplus> (negative b)"
    using 1 plus_assoc by auto
  have 3: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = (b \<oplus> Z) \<oplus> (negative b)"
    using 2 negation by auto
  have 4: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = (b ) \<oplus> (negative b)"
    using 3 plus_ident by auto
  have 5: "(b \<ominus> a)  \<oplus> (a \<ominus> b) = Z"
    using 4 negation by auto
  have 6: "(a \<ominus> b)  \<oplus> (b \<ominus> a) = Z"
    using 5 plus_commute by auto
  show ?thesis using 6 unique_negative by auto
qed

lemma help3: 
  fixes a b
  assumes "(negative (a \<ominus> b)) \<in> P"
  shows "gt b a"
proof -
  have 0: "negative (a \<ominus> b) = b \<ominus> a" using  negsub by metis
  have 1: "b \<ominus> a \<in> P" using assms 0 by auto
  show ?thesis using 1 gt_def by auto 
qed


lemma help3b: 
  fixes a b
  assumes "gt b a"
  shows "(negative (a \<ominus> b)) \<in> P"
proof -
  have 0: "b \<ominus> a \<in> P" using assms gt_def by auto
  have 1: "negative (a \<ominus> b) = b \<ominus> a" using  negsub by metis
  have 2: "negative (a \<ominus> b) \<in> P" using 0 1  by auto
  show ?thesis using 2 gt_def by auto 
qed

lemma help3c:
  fixes a b
  shows "gt b a = ((negative (a \<ominus> b)) \<in> P)"
proof -
  show ?thesis using help3 help3b by auto
qed

lemma trichotomy3:
  fixes a b
  assumes "h1 = (a = b)" and "h2 = (gt a b)" and "h3 = (gt b a)"
  shows "(h1 \<and> \<not>( h2 \<or> h3)) \<or> 
(h2 \<and> \<not>( h1 \<or> h3)) \<or> 
(h3 \<and> \<not>( h1 \<or> h2))"
proof -
  have 0: "(a \<ominus> b = Z \<and> \<not>( a \<ominus> b \<in> P \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( a \<ominus> b = Z \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
((negative (a \<ominus> b)) \<in> P \<and> \<not>( a \<ominus> b = Z \<or> a \<ominus> b \<in> P))" using  trichotomy2 assms by auto
  have 1: "(a = b \<and> \<not>( a \<ominus> b \<in> P \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( a \<ominus> b = Z \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
((negative (a \<ominus> b)) \<in> P \<and> \<not>(  a \<ominus> b = Z \<or> a \<ominus> b \<in> P))" 
    using  0 help1 by auto
  have 2: "(a = b \<and> \<not>( a \<ominus> b \<in> P \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( (a = b) \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
((negative (a \<ominus> b)) \<in> P \<and> \<not>(  (a = b) \<or> a \<ominus> b \<in> P))" 
    using  1 help1 by (metis negsub)
  have 3: "(h1 \<and> \<not>( a \<ominus> b \<in> P \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( h1 \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
((negative (a \<ominus> b)) \<in> P \<and> \<not>( h1 \<or> a \<ominus> b \<in> P))" 
    using  2 assms(1) by auto
  have 4: " a \<ominus> b \<in> P = gt a b" using gt_def by auto
  have 5: "(h1 \<and> \<not>(gt a b \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
(gt a b \<and> \<not>( h1 \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
((negative (a \<ominus> b)) \<in> P \<and> \<not>( h1 \<or> gt a b))" 
    using  3 4 by auto 
  have 6 :"(negative (a \<ominus> b) \<in> P) = h3" using help3c assms by auto
  have 7 :"(h1 \<and> \<not>(gt a b \<or> h3)) \<or>
(gt a b \<and> \<not>( h1 \<or>  h3)) \<or>
(h3 \<and> \<not>( h1 \<or> gt a b))"  using 5 6 by auto
  show ?thesis using 7 assms gt_def by auto
qed



lemma neg_sum:
  fixes a b
  shows "negative (a  \<oplus> c) = (negative a)  \<oplus> (negative c)"
proof -
  have 0: "(a  \<oplus> c) \<oplus> ( (negative a)  \<oplus> (negative c)) = Z" 
  proof -
    have 1: "(a  \<oplus> c) \<oplus> ( (negative a)  \<oplus> (negative c)) = ((a  \<oplus> c) \<oplus>  (negative a))  \<oplus> (negative c)"
      using plus_assoc  by auto
    have 2: "(a  \<oplus> c) \<oplus> ( (negative a)  \<oplus> (negative c)) = (a  \<oplus> (c \<oplus>  (negative a)))  \<oplus> (negative c)"
      using plus_assoc 1  by auto
    have 3: "(a  \<oplus> c) \<oplus> ( (negative a)  \<oplus> (negative c)) = (a  \<oplus> ((negative a) \<oplus> c))  \<oplus> (negative c)"
      using plus_commute 2  by auto
    have 4: "(a  \<oplus> c) \<oplus> ( (negative a)  \<oplus> (negative c)) = ((a  \<oplus> (negative a)) \<oplus> c)  \<oplus> (negative c)"
      using plus_assoc 3  by auto
    have 5: "(a  \<oplus> c) \<oplus> ( (negative a)  \<oplus> (negative c)) = (Z \<oplus> c)  \<oplus> (negative c)"
      using  negation 4  by auto
    have 6: "(a  \<oplus> c) \<oplus> ( (negative a)  \<oplus> (negative c)) = Z \<oplus> (c  \<oplus> (negative c))"
      using  plus_assoc 5  by auto
    have 7: "(a  \<oplus> c) \<oplus> ( (negative a)  \<oplus> (negative c)) = Z \<oplus> Z"
      using  negation 6  by auto
    show ?thesis
      using  plus_ident 7  by auto
  qed
  show ?thesis using 0 unique_negative by auto 
qed

(* jfh: this is the result Spivak describes as "slightly more interesting" 
near the end of the material before the traingle inequality *)
lemma slightly_more_interesting:
  fixes a b c
  assumes "lt a b"
  shows "lt (a  \<oplus> c) (b  \<oplus> c)"
proof -
  have 0:"(b  \<ominus> a) \<in> P" using assms lt_def gt_def by auto
  have 1: "b  \<oplus> (negative a) \<in> P" using 0 diff_def by auto
  have 2: "(b  \<oplus> (negative a))  \<oplus> (c  \<oplus> (negative c)) \<in> P" 
    using 1 negation plus_ident by auto
  have 3: "((b  \<oplus> (negative a))  \<oplus> c)  \<oplus> (negative c) \<in> P" 
    using  2 plus_assoc by auto
  have 4: "(b  \<oplus> ((negative a)  \<oplus> c))  \<oplus> (negative c) \<in> P" 
    using  3 plus_assoc by auto
  have 5: "(b  \<oplus> (c  \<oplus> (negative a)))  \<oplus> (negative c) \<in> P" 
    using 4 plus_commute by auto
  have 6: "((b  \<oplus> c)  \<oplus> (negative a))  \<oplus> (negative c) \<in> P" 
    using 5 plus_assoc by auto
  have 7: "(b  \<oplus> c)  \<oplus> ((negative a)  \<oplus> (negative c)) \<in> P" 
    using 6 plus_assoc by auto
  have 8: "(b  \<oplus> c)  \<oplus> (negative (a  \<oplus> c)) \<in> P" 
    using 7 neg_sum by auto
  have 9: "(b  \<oplus> c)  \<ominus>  (a  \<oplus> c)   \<in> P" 
    using 8 diff_def by auto
  show ?thesis using diff_def 9 lt_def gt_def by auto
qed

lemma almost_done: 
  fixes a b c
  assumes "lt a b" and "lt b c"
  shows "lt a  c"
proof -
  have 0:"(b  \<ominus> a) \<in> P" using assms(1) lt_def gt_def by auto
  have 1:"(c  \<ominus> b) \<in> P" using assms(2) lt_def gt_def by auto
  have 2:"(c  \<ominus> b)  \<oplus> (b  \<ominus> a) \<in> P" using 0 1 additive_closure by auto
  have 3:"(c  \<oplus> (negative b))  \<oplus> (b   \<oplus> (negative a)) \<in> P" using 2 diff_def by auto
  have 4:"c  \<oplus> ((negative b)  \<oplus> (b   \<oplus> (negative a))) \<in> P" using 3 plus_assoc by auto
  have 5:"c  \<oplus> (((negative b)  \<oplus> b)   \<oplus> (negative a)) \<in> P" using 4 plus_assoc by auto
  have 6:"c  \<oplus> (Z   \<oplus> (negative a)) \<in> P" using 5 negation by auto
  have 7:"c  \<oplus> (negative a) \<in> P" using 6 plus_ident by auto
  have 8:"(c  \<ominus> a) \<in> P" using 7 diff_def by auto
  show ?thesis using 8 lt_def gt_def by auto
qed

(* This is my shorthand for the "nonnegative" numbers, hence NN *)
definition NN where "NN = P \<union> {Z}"

lemma NN_closure:
  fixes a b
  assumes "a \<in>  NN"
  assumes "b \<in>  NN"
  assumes "b \<in>  NN"
  shows "a  \<oplus> b  \<in>  NN"
proof (cases "a = Z")
  case True
  have 0: "a  \<oplus> b = b" using True plus_ident by auto
  have 1: "b  \<in>  NN" using assms by auto
  then show ?thesis using 0 1 by auto
next
  case False
  have aPos: "a \<in> P" using False NN_def assms 
    by auto
  then show ?thesis 
  proof (cases "b = Z")
    case True
    have 1: "a  \<oplus> b = a"  using True plus_ident by auto
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
  assumes "ge a b"
  shows "a  \<ominus> b  \<in>  NN"
proof -
  have 00:"ge a b" using assms(1) le_def by auto  
  have 01:"(a  \<ominus> b) \<in> P \<or> a = b" using 00  ge_def by auto 
  have 02:"(a  \<ominus> b) \<in> P \<or> (a  \<ominus> b) \<in>  {Z}" using 01 diff_def negation negZ by auto 
  have 0:"(a \<ominus> b) \<in> NN" using 02 NN_def by auto
  then show ?thesis by auto
qed

lemma ge_NN:
  fixes a b
  assumes "a  \<ominus> b  \<in>  NN"
  shows "ge a b"
proof -
  have 01:"a  \<ominus> b  \<in>  NN" using assms(1) by auto
  have 02:"(a  \<ominus> b) \<in> P \<or> (a  \<ominus> b) = Z" using 01 NN_def by auto 
  have 03:"(a  \<ominus> b) \<in> P \<or> (a \<oplus> negative b) = Z" using 02  diff_def negation by auto
  have 04:"(a  \<ominus> b) \<in> P \<or> (a \<oplus> negative b)\<oplus> b = Z\<oplus> b" using 03  by auto
  have 05:"(a  \<ominus> b) \<in> P \<or> (a \<oplus> (negative b\<oplus> b)) = Z\<oplus> b" using 04 plus_assoc  by auto
  have 06:"(a  \<ominus> b) \<in> P \<or> (a \<oplus> Z) = b" using 05 plus_ident negation  by auto
  have 06:"(a  \<ominus> b) \<in> P \<or> a = b" using 06 plus_ident by auto
  have 00:"ge a b" using 06 ge_def by auto  
  then show ?thesis by auto
qed

lemma almost_done_le: 
  fixes a b c
  assumes "le a b" and "le b c"
  shows "le a  c"
proof -
 
  have 00:"ge b a" using assms(1) le_def by auto  
  have 0:"(b \<ominus> a) \<in> NN" using 00 NN_ge by auto

  have 10:"ge c b" using assms(2) le_def by auto  
  have 1:"(c  \<ominus> b) \<in> NN" using 10 NN_ge by auto
  have 2:"(c  \<ominus> b)  \<oplus> (b  \<ominus> a) \<in> NN" using 0 1 additive_closure NN_def 
    using NN_closure by auto
  have 3:"(c  \<oplus> (negative b))  \<oplus> (b   \<oplus> (negative a)) \<in> NN" using 2 diff_def by auto
  have 4:"c  \<oplus> ((negative b)  \<oplus> (b   \<oplus> (negative a))) \<in> NN" using 3 plus_assoc by auto
  have 5:"c  \<oplus> (((negative b)  \<oplus> b)   \<oplus> (negative a)) \<in> NN" using 4 plus_assoc by auto
  have 6:"c  \<oplus> (Z   \<oplus> (negative a)) \<in> NN" using 5 negation by auto
  have 7:"c  \<oplus> (negative a) \<in> NN" using 6 plus_ident by auto
  have 8:"(c  \<ominus> a) \<in> NN" using 7 diff_def by auto
  have 9: "ge c a" using 8 ge_NN by auto
  have 10: "le a c" using 9 le_def by simp
  then show ?thesis by auto
qed

lemma neg_prod_pos:
  fixes a b
  assumes "lt a Z" and "lt b Z"
  shows "gt (a  \<odot> b) Z"
proof -
  have 0: "gt Z a" using assms lt_def by auto
  have 1: "gt Z b" using assms lt_def by auto

  have 2: "Z  \<ominus>  a \<in> P" using 0 gt_def by auto
  have 3: "Z  \<ominus>  b \<in> P" using 1 gt_def by auto
  have 4: "negative a \<in> P" using 2 diff_def plus_ident by auto
  have 5: "negative b \<in> P" using 3 diff_def plus_ident by auto
  hence "(negative a  \<odot>  negative b) \<in> P" using 4  multiplicative_closure by auto
  hence  "(a  \<odot>  b) \<in> P" using negative_product  by auto
  hence  "(a  \<odot>  b) \<oplus> Z \<in> P" using plus_ident  by auto
  hence  "(a  \<odot>  b) \<oplus> (negative Z) \<in> P" using negZ  by auto
  hence 10:  "(a  \<odot>  b)  \<ominus>  Z \<in> P" using diff_def  by auto 
  show ?thesis  using 10 gt_def by auto
qed

(*
lemma neg_prod_pos:
  fixes a b
  assumes "lt a Z" and "lt b Z"
  shows "gt (a  \<odot> b) Z"
proof -
  have 0: "gt Z a" using assms lt_def by auto
  have 1: "gt Z b" using assms lt_def by auto

  have 2: "Z  \<ominus>  a \<in> P" using 0 gt_def by auto
  have 3: "Z  \<ominus>  b \<in> P" using 1 gt_def by auto
  have 4: "negative a \<in> P" using 2 diff_def plus_ident by auto
  have 5: "negative b \<in> P" using 3 diff_def plus_ident by auto
  have 6: "(negative a  \<odot>  negative b) \<in> P" 
    using 4 5 multiplicative_closure  by auto
  have 7:  "(a  \<odot>  b) \<in> P" using 6 negative_product by auto
  have 8:  "(a  \<odot>  b) \<oplus> Z \<in> P" using 7 plus_ident by auto
  have 9:  "(a  \<odot>  b) \<oplus> (negative Z) \<in> P" using 8 negZ by auto
  have 10:  "(a  \<odot>  b)  \<ominus>  Z \<in> P" using 9 diff_def by auto
  show ?thesis using 10 gt_def by auto 
qed
*)
lemma square_pos:
  fixes b
  assumes "b \<noteq> Z"
  shows "gt (b \<odot> b)  Z"
proof -
  have 0: "b \<in> P \<or> (negative b) \<in> P" using assms trichotomy by auto
  show ?thesis
  proof (cases "b \<in> P")
    case True
    have "(b \<odot> b) \<in> P" using True multiplicative_closure by auto
    hence "(b \<odot> b)  \<oplus> Z  \<in> P" using plus_ident by auto
    hence "(b \<odot> b)  \<oplus> (negative Z)  \<in> P" using negZ  by auto
    hence "(b \<odot> b)  \<ominus>  Z  \<in> P" using diff_def  by auto
    
    then show ?thesis using gt_def by auto
  next
    case False
    have "(negative b) \<in> P" using 0 False by auto
    hence "lt b Z" using lt_def gt_def 
      by (simp add: plus_ident(2) diff_def)
    then show ?thesis using neg_prod_pos by auto 
  qed
qed

lemma one_pos:
  shows "gt U  Z"
proof -
  have "U \<noteq> Z" using mul_ident by simp
  hence "gt (U \<odot> U) Z" using square_pos by auto
  then show ?thesis using mul_ident by auto
qed

definition abs  where
"abs a  \<equiv> (if gt a Z then a else negative a)"

(* jfh: I tried to do a by-cases proof of the triangle inequality,
but found myself muddled up in the cases, So I wrote a tiny 
lemma for each case, where I assumed a and b were both nonnegative, 
or that one was negative and the other nonnegative, etc. These are called
ti1, ti2, ti3, ti4, one fore each case *)

lemma ti1:
  fixes a::r and  b
  assumes "Nab = abs (a \<oplus> b)" 
  assumes "Na = abs a" 
  assumes "Nb = abs b" 
  assumes "ge a Z"
  assumes "ge b Z"
  shows "le Nab (Na  \<oplus> Nb)" 
proof -
  have 0: "Na = a" using abs_def assms  ge_def gt_def negZ by force
  have 1: "Nb = b" using abs_def assms  ge_def gt_def negZ by force
  have 2: "ge  (a \<oplus> b) Z" using assms ge_def gt_def additive_closure 
    by (metis ex3 plus_commute subtractZ3)
  have 3: "Nab =  (a \<oplus> b)" using abs_def 2 ge_def gt_def assms negZ by auto
  have 4: "Nab =  (Na \<oplus> Nb)" using 3 0 1 by auto
  have 5: "le Nab (Na \<oplus> Nb)" using 4 le_def ge_def by auto
  show ?thesis using 5 by auto
qed

lemma negneg:
  fixes a::r 
  shows "negative (negative a) = a"
proof -
  have 0: "(negative a)  \<oplus> a = Z" using unique_negative negation by auto
  have 1: "negative (negative a) = a" using 0 unique_negative by auto
  show ?thesis using 1 by auto
qed

lemma ti2:
  fixes a::r and  b
  assumes "Nab = abs (a \<oplus> b)" 
  assumes "Na = abs a" 
  assumes "Nb = abs b" 
  assumes "lt a Z"
  assumes "lt b Z"
  shows "le Nab (Na  \<oplus> Nb)" 
proof -
  have 0: "Na = negative a" using abs_def assms  ge_def gt_def lt_def negZ 
    by (meson help3b trichotomy)
  have 1: "Nb = negative b" using  abs_def assms  ge_def gt_def lt_def negZ  by (meson help3b trichotomy)
  have 2: "lt  (a \<oplus> b) Z" using assms ge_def gt_def lt_def additive_closure
    by (metis plus_ident(1) diff_def ex3 negsub)
  have 3: "Nab = negative (a \<oplus> b)" using abs_def 2 ge_def gt_def lt_def assms negZ 
    using trichotomy3 by fastforce
  have 4: "negative (a \<oplus> b) = (negative a) \<oplus> (negative b)"  using neg_sum by auto 
  have 5: "Nab = (Na \<oplus> Nb)" using 0 1 3 4  by auto
  have 6: "le Nab (Na \<oplus> Nb)" using 5 le_def ge_def by auto
  show ?thesis using 6 by auto
qed

lemma ti3:
  fixes a::r and  b
  assumes "Sab = a \<oplus> b" 
  assumes "Nab = abs (a \<oplus> b)" 
  assumes "Na = abs a" 
  assumes "Nb = abs b" 
  assumes "ge a Z"
  assumes "lt b Z"
  assumes "gt Sab Z"
  shows "le Nab (Na  \<oplus> Nb)" 
proof -
  have 0: "Na =  a" using abs_def assms  ge_def gt_def lt_def negZ by auto
  have 1: "Nb = negative b" using  abs_def assms  ge_def gt_def lt_def negZ 
    using trichotomy3 by fastforce
  have 2: "gt  (a \<oplus> b) Z" using assms by auto 
  have 3: "Nab = (a \<oplus> b)" using abs_def 2 ge_def gt_def lt_def assms negZ 
    using trichotomy3 by fastforce
  have 4: "lt b (negative b)" using assms lt_def
    by (simp add: additive_closure plus_ident(2) diff_def gt_def)
  have 5: "lt (b \<oplus> a)  ((negative b) \<oplus> a)" using 4 assms le_def lt_def gt_def slightly_more_interesting by auto
  have 6: "lt (a \<oplus> b)  (a \<oplus> (negative b))" using 5 plus_commute by auto
  have 7: "lt Nab (Na \<oplus> Nb)" using 6 le_def 3 0 1 by auto
  have 8: "le Nab (Na \<oplus> Nb)" using 7 le_def ge_def lt_def gt_def by auto
  then show ?thesis using 8 by auto
qed

lemma ti4:
  fixes a::r and  b
  assumes "Sab = a \<oplus> b" 
  assumes "Nab = abs (a \<oplus> b)" 
  assumes "Na = abs a" 
  assumes "Nb = abs b" 
  assumes "ge a Z"
  assumes "lt b Z"
  assumes "le Sab Z"
  shows "le Nab (Na  \<oplus> Nb)" 
proof - 
  have 0: "Na =  a" using abs_def assms  ge_def gt_def lt_def negZ by auto
  have 1: "Nb = negative b" using  abs_def assms  ge_def gt_def lt_def negZ 
    using trichotomy3 by fastforce
  have 2: "le  (a \<oplus> b) Z" using assms by auto 
  have 3: "Nab = ((negative a)  \<ominus>  b)" using diff_def abs_def 2 ge_def gt_def lt_def assms negZ 
    trichotomy3   by (metis le_def neg_sum) 
  have 4: "le (negative a) Z" using assms(5) le_def 
    by (metis ge_def   negsub subtractZ3)
  have 5: "le  Z a" using assms(5) le_def by auto
  have 6: "le (negative a) a"
    using "4" "5" almost_done_le by blast  
  have 7: "le ((negative a)  \<ominus> b)  (a  \<ominus> b)" using 6 assms le_def lt_def gt_def diff_def ge_def 
      slightly_more_interesting by auto
  have 8: "le ((negative a)  \<ominus> b)  (a \<oplus> (negative b))" using 7 plus_commute diff_def by auto
  have 9: "le Nab (Na \<oplus> Nb)" using 8 le_def 3 0 1 by auto
  have 10: "le Nab (Na \<oplus> Nb)" using 9 le_def by auto
  then show ?thesis using 10 by auto 
qed

(* jfh: to finish up the proof of the triangle inequality,
I confess that in places I used "sledgehammer", and to make it 
get the job done, I needed these lemmas. They're all more or less the
same, so you should feel free to assemble a team of friends and each prove one 
of them *)

lemma ge_lt:
  fixes b
  assumes "(\<not> ge b Z)"
  shows "lt b Z"
proof -
  have 0:  "\<not>((b \<ominus> Z)  \<in> P) \<and> (b \<noteq> Z)" using assms ge_def by simp
  have 1:  "\<not>((b \<ominus> Z)  \<in> P)" using 0 by simp
  have 2:  "\<not>(b  \<in> P)" using 1 subtractZ3 by auto
  have 3: " (negative b) \<in> P" using 0 2 trichotomy by auto
  have 4: " (negative b) = Z \<ominus> b"  using diff_def plus_ident by auto
  show ?thesis using gt_def 4 3 lt_def by auto
qed

lemma gt_le:
  fixes b
  assumes "(\<not> gt b Z)"
  shows "le b Z"
proof -
  have 0:  "\<not>((b \<ominus> Z)  \<in> P)" using assms gt_def by simp
  have 1:  "\<not>((b \<ominus> Z)  \<in> P)" using 0 by simp
  have 2:  "\<not>(b  \<in> P)" using 1 subtractZ3 by auto
  have 3: " (negative b) \<in> P \<or> b = Z " using 0 2 trichotomy by auto
  have 4: " (negative b) = Z \<ominus> b"  using diff_def plus_ident by auto
  have 5: " Z \<ominus> b \<in> P \<or>  b = Z " using 3 4 diff_def by argo
  show ?thesis using gt_def 5 le_def lt_def ge_def by blast 
qed

lemma le_gt:
  fixes b
  assumes "(\<not> le b Z)"
  shows "gt b Z"
proof -
(* "le a b = (lt a b \<or> a = b)" *)
  have 0:  "\<not>(lt b Z \<or> b = Z)" using assms le_def lt_def gt_def ge_def by auto
  have 1:  "\<not>(((Z \<ominus> b)  \<in> P) \<and> b = Z)" using 0 lt_def gt_def le_def by auto
  have 2:  "\<not>( b = Z \<and> ((Z \<ominus> b)  \<in> P))" using 1  by auto
  have 3:  "\<not>( b = Z \<and> ((negative b)  \<in> P))" using 2 0 negation diff_def by auto
  have 4: "(b = Z \<and> \<not>( b \<in> P \<or>  (negative b) \<in> P)) \<or>
  (b \<in> P \<and> \<not>( b = Z \<or>  (negative b) \<in> P)) \<or>
((negative b) \<in> P \<and> \<not>( b = Z \<or> b \<in> P))" using trichotomy by auto
  have 5: "b \<in> P" using 3 4
    using assms gtP1 gt_le by blast
  then show ?thesis using gtP2 by auto
qed


lemma lt_ge:
  fixes b
  assumes "(\<not> lt b Z)"
  shows "ge b Z"
proof -
  have 0: "\<not> (lt b Z)" using assms by auto
  have 1: "Z \<ominus> b \<notin> P" using lt_def gt_def 0 by auto
  have 2: "Z \<ominus> b = Z \<or> (negative (Z \<ominus> b)) \<in> P" using 1 trichotomy ge_def by auto
  have 3: "Z \<ominus> b = Z \<or> (negative (Z \<ominus> b)) \<in> P" using 2 diff_def plus_ident by auto
  have 4: "Z \<oplus>negative  b = Z \<or> (negative (Z \<ominus> b)) \<in> P" using 3 diff_def plus_ident by auto
  have 5: "negative  b = Z \<or> (negative (Z \<ominus> b)) \<in> P" using 4 diff_def plus_ident by auto
  have 6: "negative (negative  b) = negative Z \<or> (negative (Z \<ominus> b)) \<in> P" using 5 negation by auto
  have 7: "  b = negative Z \<or> (negative (Z \<ominus> b)) \<in> P" using 6 negneg by auto
  have 8: "  b = Z \<or> (negative (Z \<ominus> b)) \<in> P" using 7 negZ by auto
  have 9: "  b = Z \<or> (b \<ominus> Z) \<in> P" using 8 negsub by metis
  have 10: "b \<ominus> Z \<in> P\<or> b = Z" using 9 by auto
  have 11: "ge b Z" using 10 ge_def trichotomy negation by auto
  then show ?thesis by auto
qed

lemma triangle_inequality_spivak2:
  fixes a::r and  b
  assumes "Nab = abs (a \<oplus> b)" 
  assumes "Na = abs a" 
  assumes "Nb = abs b" 
  shows "le Nab (Na  \<oplus> Nb)" 
proof (cases "ge a Z")
  case True
  have aPos:  "ge a Z" using True by auto
  then show ?thesis 
  proof (cases "ge b Z")
    case True
    have bPos:  "ge b Z" using True by auto
    then show ?thesis using aPos ti1 
      assms(1) assms(2) assms(3) by blast      
  next
    case False
    have bNeg:  "\<not>(ge b Z)" using False by auto
    then show ?thesis using aPos ti3
      assms(1) assms(2) assms(3)
      by (metis ge_lt gt_le ti4)       
  qed
next
  case False
  have aNeg:  "\<not> (ge a Z)" using False by auto
  then show ?thesis 
  proof (cases "ge b Z")
    case True
    have bPos:  "ge b Z" using True by auto
    then show ?thesis using aNeg bPos 
      assms(1) assms(2) assms(3)
      by (metis assms(1) assms(2) assms(3) ge_lt gt_le plus_commute ti3 ti4)      
  next
    case False
    have bNeg:  "\<not>(ge b Z)" using False by auto
    then show ?thesis using aNeg bNeg
      by (simp add: assms(1) assms(2) assms(3) ge_lt ti2) 
  qed
qed

end
