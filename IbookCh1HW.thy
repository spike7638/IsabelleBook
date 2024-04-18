theory IbookCh1HW
  imports Main
begin

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

(* EXERCISE: show that (2) = (3) as described. I'll get you started ...*)

lemma ex1: 
  fixes a::r and b::r and c::r and d::r
  shows "(a \<oplus> (b \<oplus> c)) \<oplus> d =  a \<oplus> ((b \<oplus> c) \<oplus> d)"
sorry
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

(* EXERCISE: Formulate the theorem above, and write the proof. *)

(* As we have just hinted, it is convenient to regard 
subtraction as an operation derived from addition; we consider
a - b to be an abbreviation for a + (-b). 
*)

definition diff:: "r \<Rightarrow> r \<Rightarrow> r" where
"diff a b \<equiv> (a \<oplus> (negative b))"

notation diff (infix "\<ominus>" 80) 
(* jfh: when you define diff like this, a new 'fact' is introduced on your
behalf, called "diff_def". There isn't a "negative_def" because we didn't actually give
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

(* EXERCISE: Spivak has an advantage over us here: for him the numbers
3 and 5 already exist, and his readers know that 5 - 3 = 2. We lack 
explicit constants for any numbers except Z and U. We can still, however,
mimic this computation, just in greater generality. Show that
if x + a = b, then x = b - a, following Spivak's computation. *)

lemma insert_name_here: 
  fixes x::r and a and b
  assumes "x \<oplus> a = b"
  shows "x = b \<ominus> a"
  sorry

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

(* Math EXERCISE: try to check this. See if you can find a 
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

(* EXERCISE: Write P6 (giving it the name 'mul_ident' as a lemma, using 
'sorry' as a proof; mimic the format of prior property-lemmas. Be
sure to include three separate conclusions in your "shows" line. *)

lemma mul_ident:  (* P6 *)
  fixes ...
  shows ... and ... and ...
  sorry

(* jfh: here are the remaining three facts about multiplication *)
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
0^{-1} is meaningless---division by 0 is ALWAYS undefined. 
*)

(*jfh: This is a place where Isabelle and other proof assistants diverge
from conventional mathematical practice. They actually DO define the 
multiplicative inverse using a function on ALL real numbers. But they
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

(* EXERCISE: mimic the proof above in Isabelle, using "inv" as the 
multiplicative inverse. Make sure to carefully note where you use the 
fact that a is nonzero. This is an example of why it doesn't matter 
if an inverse for 0 is 'defined' ... if it cannot be used for anything!
*)

lemma ex6: 
  fixes a::r and b and c
  assumes "a \<odot> b = a \<odot> c" and "a \<noteq> Z"
  shows "b = c"
  sorry

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
EXERCISE: Mimic that last proof in Isabelle, trying to copy the structure
of the "cases" proof near the end of Chapter 0. Use
   proof cases ("a = 0")
You may find yourself wanting to prove a preparatory lemma (I did). 
*)

lemma prep1: 
  fixes a::r
  shows "a \<odot> Z = Z"
  sorry
lemma ex7:
  fixes a::r and b
  assumes "a \<odot> b = Z" 
  shows "(a = Z) \<or> (b = Z)"
  sorry

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
  sorry

lemma unique_negative:
  fixes a b
  assumes "u  \<oplus> x = Z"
  shows "x = negative u"
  sorry

lemma move_negative: 
  fixes a b
  shows "(negative a)  \<odot> b = negative (a  \<odot> b)"
  sorry

lemma negative_product: 
  fixes a b
  shows "(negative a)  \<odot> (negative b) = a  \<odot> b"
  sorry

(* A few more warmup lemmas *)

lemma negZ:
  shows "negative Z = Z"
(*hint: Z + (negative Z) = Z; does a prior lemma then help? *)
  sorry

lemma subtractZ:
  shows "a \<ominus> Z = a  \<oplus> (negative Z)"
  sorry

lemma subtractZ2:
  shows "a \<ominus> Z = a  \<oplus> Z"
  sorry

lemma subtractZ3:
  shows "a \<ominus> Z = a"
  sorry

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
  sorry

lemma gtP2:
  assumes "a \<in> P"
  shows "gt a Z"
  sorry

lemma trichotomy2: 
  fixes a b
  shows "(a \<ominus> b = Z \<and> \<not>( a \<ominus> b \<in> P \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( a \<ominus> b = Z \<or>  (negative (a \<ominus> b)) \<in> P)) \<or>
((negative (a \<ominus> b)) \<in> P \<and> \<not>( a \<ominus> b = Z \<or> a \<ominus> b \<in> P))"
  sorry

lemma help1: 
  fixes a b
  assumes "a \<ominus> b = Z"
  shows "a = b"
  sorry

lemma help2: 
  fixes a b
  assumes "a \<ominus> b \<in> P"
  shows "gt a b"
  sorry

lemma negsub:
  fixes a b
  shows "b \<ominus> a = negative (a \<ominus> b)"
  sorry

lemma help3: 
  fixes a b
  assumes "(negative (a \<ominus> b)) \<in> P"
  shows "gt b a"
  sorry

lemma help3b: 
  fixes a b
  assumes "gt b a"
  shows "(negative (a \<ominus> b)) \<in> P"
  sorry

lemma help3c:
  fixes a b
  shows "gt b a = ((negative (a \<ominus> b)) \<in> P)"
  sorry 

lemma trichotomy3:
  fixes a b
  assumes "h1 = (a = b)" and "h2 = (gt a b)" and "h3 = (gt b a)"
  shows "(h1 \<and> \<not>( h2 \<or> h3)) \<or> 
(h2 \<and> \<not>( h1 \<or> h3)) \<or> 
(h3 \<and> \<not>( h1 \<or> h2))"
  sorry


lemma neg_sum:
  fixes a b
  shows "negative (a  \<oplus> c) = (negative a)  \<oplus> (negative c)"
  sorry

(* jfh: this is the result Spivak describes as "slightly more interesting" 
near the end of the material before the traingle inequality *)
lemma slightly_more_interesting:
  fixes a b c
  assumes "lt a b"
  shows "lt (a  \<oplus> c) (b  \<oplus> c)"
  sorry

lemma almost_done: 
  fixes a b c
  assumes "lt a b" and "lt b c"
  shows "lt a  c"
  sorry

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
  ...
  then show ?thesis using ... by auto
next
  case False
  ...
  then show ?thesis 
  proof (cases "b = Z")
    ...
qed

lemma NN_ge:
  fixes a b
  assumes "ge a b"
  shows "a  \<ominus> b  \<in>  NN"
  sorry

lemma ge_NN:
  fixes a b
  assumes "a  \<ominus> b  \<in>  NN"
  shows "ge a b"
  sorry

lemma almost_done_le: 
  fixes a b c
  assumes "le a b" and "le b c"
  shows "le a  c"
  sorry

lemma neg_prod_pos:
  fixes a b
  assumes "lt a Z" and "lt b Z"
  shows "gt (a  \<odot> b) Z"
  sorry

lemma square_pos:
  fixes b
  assumes "b \<noteq> Z"
  shows "gt (b \<odot> b)  Z"
proof -
  have 0: "b \<in> P \<or> (negative b) \<in> P" using assms trichotomy by auto
  show ?thesis
  proof (cases "b \<in> P")
    ...
  qed
qed

lemma one_pos:
  shows "gt U  Z"
  sorry

definition abs  where
"abs a  \<equiv> (if gt a Z then a else negative a)"

(* jfh: I tried to do a by-cases proof of the triangle inequality,
but found myself muddled up in the cases, So I wrote a tiny 
lemma for each case, where I assumed a and b were both nonnegative, 
or that one was negative and the other nonnegative, etc. These are called
ti1, ti2, ti3, ti4, one for each case *)

(* jfh: I should also confess that at this point things just got messy,
and I used sledgehammer occasionally to help out. *)
lemma ti1:
  fixes a::r and  b
  assumes "Nab = abs (a \<oplus> b)" 
  assumes "Na = abs a" 
  assumes "Nb = abs b" 
  assumes "ge a Z"
  assumes "ge b Z"
  shows "le Nab (Na  \<oplus> Nb)" 
  sorry

lemma negneg:
  fixes a::r 
  shows "negative (negative a) = a"
  sorry

lemma ti2:
  fixes a::r and  b
  assumes "Nab = abs (a \<oplus> b)" 
  assumes "Na = abs a" 
  assumes "Nb = abs b" 
  assumes "lt a Z"
  assumes "lt b Z"
  shows "le Nab (Na  \<oplus> Nb)" 
  sorry

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
  sorry

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
  sorry

(* jfh: to finish up the proof of the triangle inequality,
I confess that in places I once again used "sledgehammer", and to make it 
get the job done, I needed these lemmas. They're all more or less the
same, so you should feel free to assemble a team of friends and each prove one 
of them. You should NOT need sledgehammer for these.  *)

lemma ge_lt:
  fixes b
  assumes "(\<not> ge b Z)"
  shows "lt b Z"
  sorry

lemma gt_le:
  fixes b
  assumes "(\<not> gt b Z)"
  shows "le b Z"
  sorry

lemma le_gt:
  fixes b
  assumes "(\<not> le b Z)"
  shows "gt b Z"
  sorry

lemma lt_ge:
  fixes b
  assumes "(\<not> lt b Z)"
  shows "ge b Z"
  sorry

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
