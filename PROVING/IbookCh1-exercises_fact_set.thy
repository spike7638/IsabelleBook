theory "IbookCh1-exercises_fact_set"
  imports Main
begin

(* An experiment with a fact set used to accumulate everything *)

named_theorems known

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

lemma plus_assoc [known]: (* Spivak calls this P1 *)
  fixes a::r and b::r and c::r
  shows "(a \<oplus> b) \<oplus> c =  a \<oplus> (b \<oplus> c)"
  sorry

lemma ex0  [known]: 
  fixes a::r and b::r and c::r and d::r
  shows "((a \<oplus> b) \<oplus> c) \<oplus> d =  (a \<oplus> (b \<oplus> c)) \<oplus> d"
proof -
  show ?thesis using plus_assoc by auto
qed

lemma ex1  [known]: 
  fixes a::r and b::r and c::r and d::r
  shows "(a \<oplus> (b \<oplus> c)) \<oplus> d =  a \<oplus> ((b \<oplus> c) \<oplus> d)"
proof -
  show ?thesis using plus_assoc by auto 
qed

lemma additive_ident [known]: (* Spivak calls this P2 *)
  fixes a::r
  shows "a \<oplus> Z =  a" and "Z \<oplus> a =  a"
  sorry

lemma negation [known]: (* Spivak calls this P3 *)
  fixes a::r
  shows "a \<oplus> (neg a) =  Z"
  and  "(neg a) \<oplus> a =  Z"
  sorry

lemma ex2  [known]: 
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

definition  diff:: "r \<Rightarrow> r \<Rightarrow> r" where
"diff a b \<equiv> (a \<oplus> (neg b))"  

declare diff_def [known]

notation diff  (infix "\<ominus>" 80)

lemma ex3  [known]: 
  fixes x::r and a and b
  assumes "x \<oplus> a = b"
  shows "x = b \<ominus> a"

proof -
  show ?thesis using known assms by auto
qed

(* Only one other property of addition remains to be listed. When 
considering the sums of three numbers a, b, and c, only two sums 
were mentioned: (a+b) + c and a + (b + c). Actually, several other
arrangements are obtained if the order of a, b, and c is changed. That
these sums are equal depends on 
   (P4) If and and b are any numbers, then 
             a + b = b + a.
*)

lemma plus_commute  [known]:
  fixes a::r and b::r 
  shows "(a \<oplus> b) =  (b \<oplus> a)"
  sorry

lemma mul_assoc  [known]: (* P5 *)
  fixes a::r and b::r and c::r
  shows "((a \<odot> b) \<odot> c) =  (a \<odot> (b \<odot> c))"
  sorry

(* EXERCISE 5: Write P6 (giving it the name 'mul_ident' as a lemma, using 
'sorry' as a proof; mimic the format of prior property-lemmas. Be
sure to include three separate conclusions in your "shows" line. Use the 
name "U" (for 'unit') instead of "1". *)
lemma mul_ident  [known]:  (* P6 *)
  fixes a::r
  shows "a \<odot> U =  a" and "U \<odot> a =  a" and "Z \<noteq> U"
  sorry

lemma inversion [known]: (* P7 *)
  fixes a::r
  assumes "a \<noteq> Z"
  shows "a \<odot> (reciprocal a) =  U" and "(reciprocal a) \<odot>  a =  U"
  sorry

lemma mul_commute [known]: (* P8 *)
  fixes a::r and b::r 
  shows "(a \<odot> b) =  (b \<odot> a)"
  sorry

lemma distrib [known]:
  fixes a::r and b::r and c::r
  shows "(a \<odot> (b \<oplus> c)) =  ((a \<odot> b) \<oplus> (a \<odot> c))"
  sorry


lemma ex6 [known]: 
  fixes a::r and b and c
  assumes "a \<odot> b = a  \<odot> c" and "a \<noteq> Z"
  shows "b = c"
proof -
  show ?thesis using  known assms by metis
qed

lemma ex7a  [known]: 
  fixes a::r
  shows "a \<odot> Z = Z"
proof -
  have 0: "Z \<oplus> Z = Z" using additive_ident by auto
  have 1: " a \<odot> (Z \<oplus> Z) = a \<odot> Z" using 0 by auto
  have 2: " (a \<odot> Z) \<oplus> (a \<odot> Z) = a \<odot> Z" using 1 distrib by auto
  show ?thesis  using 2 ex2 by blast
qed

lemma ex7 [known]:
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

lemma mulZ [known]: 
  fixes a
  shows "(a  \<odot> Z) = Z" and "(Z  \<odot> a) = Z"
proof -
  have 0:"Z  \<oplus> Z = Z" using additive_ident by auto
  show "a \<odot> Z = Z" using known  by meson
  show "Z \<odot> a = Z" using known  by metis
qed

lemma unique_neg [known]:
  fixes a b
  assumes "u  \<oplus> x = Z"
  shows "x = neg u"
proof -
  show ?thesis using known assms  by metis
qed


lemma negneg [known]:
  fixes a::r 
  shows "neg (neg a) = a"
proof -
  show ?thesis using known  by metis
qed

lemma move_neg [known]: 
  fixes a b
  shows "(neg a)  \<odot> b = neg(a  \<odot> b)"
proof -
  show ?thesis using known  by metis
qed

lemma neg_product [known]: 
  fixes a b
  shows "(neg a)  \<odot> (neg b) = a  \<odot> b"
proof -
  show ?thesis using known  by metis
qed

(* A few more warmup lemmas about zero, negation, and subtraction *)

lemma negZ_is_Z [known]:
  shows "neg Z = Z"
(*hint: Z + (neg Z) = Z; does a prior lemma then help? *)
proof -
  show ?thesis using known  by metis
qed

lemma subtractZ_is_identity [known]:
  shows "a \<ominus> Z = a"
proof -
  show ?thesis using known  by metis
qed

(* Additional material to get you started on positive and negative
numbers *)
consts
P::"r set"

lemma trichotomy [known]: (* Spivak's P10 *)
  fixes a
  shows "(a = Z \<and> \<not>( a \<in> P \<or>  (neg a) \<in> P)) \<or>
(a \<in> P \<and> \<not>( a = Z \<or>  (neg a) \<in> P)) \<or>
((neg a) \<in> P \<and> \<not>( a = Z \<or> a \<in> P))"
  sorry

lemma additive_closure [known]: (*Spivak's P11 *)
  fixes a b
  assumes "a \<in> P" and "b \<in> P"
  shows "a \<oplus> b \<in> P"
  sorry

lemma multiplicative_closure  [known]: (*Spivak's P12 *)
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
  where [known]: "le a b = ge b a" (* alternative way to add a definition to a fact set *)

declare gt_def[known]
declare ge_def[known]
declare lt_def[known]
declare le_def[known]

notation gt  (infix "gt" 20)
notation ge  (infix "ge" 20)
notation lt  (infix "lt" 20)
notation le  (infix "le" 20)

lemma gtP1 [known]:
  assumes "a gt Z"
  shows "a \<in> P"
proof -
  show ?thesis using known assms by metis
qed

lemma gtP2 [known]:
  assumes "a \<in> P"
  shows "a gt  Z"
proof -
    show ?thesis using known assms by metis
qed

lemma gt_le [known]:
  fixes a b
  assumes "a le b"
  shows "\<not> (a gt b)"
proof -
    show ?thesis using known assms 
    by (smt (verit))
qed

lemma le_gt [known]:
  fixes a b
  assumes "a gt b"
  shows "\<not> (a le b)"
proof -
    show ?thesis using known assms  by metis
qed

lemma lt_ge [known]:
  fixes a b
  assumes "a lt b"
  shows "\<not> (a ge b)"
proof -
    show ?thesis using known assms  by metis
qed


lemma ge_lt [known]:
  fixes a b
  assumes "a ge b"
  shows "\<not> (a lt b)"
proof -
    show ?thesis using known assms  by metis
qed

lemma trichotomy2 [known]: 
  fixes a b
  shows "(a \<ominus> b = Z \<and> \<not>( a \<ominus> b \<in> P \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( a \<ominus> b = Z \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
((neg (a \<ominus> b)) \<in> P \<and> \<not>( a \<ominus> b = Z \<or> a \<ominus> b \<in> P))"
proof -
  show ?thesis using known by presburger

qed

lemma diff_zero_equals [known]: 
  fixes a b
  assumes "a \<ominus> b = Z"
  shows "a = b"
proof -
  show ?thesis using known assms by metis
qed


lemma diff_positive_gt [known]: 
  fixes a b
  assumes "a \<ominus> b \<in> P"
  shows "a gt b"
proof -
    show ?thesis using known assms by metis
qed

lemma negsub [known]:
  fixes a b
  shows "b \<ominus> a = neg(a \<ominus> b)"
proof -
    show ?thesis using known by metis
qed

lemma trich_help3 [known]: 
  fixes a b
  assumes "(neg (a \<ominus> b)) \<in> P"
  shows "b gt a"
proof -
  show ?thesis using assms known by metis
qed


lemma trich_help3b [known]: 
  fixes a b
  assumes "b gt a"
  shows "(neg (a \<ominus> b)) \<in> P"
proof -
  show ?thesis using assms known by metis
qed

lemma trich_help3c [known]:
  fixes a b
  shows "(b gt  a) = ((neg (a \<ominus> b)) \<in> P)"
proof -
  show ?thesis using  known by metis
qed

lemma trichotomy3 [known]:
  fixes a b
  assumes "h1 = (a = b)" and "h2 = (a gt b)" and "h3 = (b gt a)"
  shows "(h1 \<and> \<not>( h2 \<or> h3)) \<or> 
        (h2 \<and> \<not>( h1 \<or> h3)) \<or> 
        (h3 \<and> \<not>( h1 \<or> h2))"
proof -
  show ?thesis using assms known by meson
qed

lemma neg_sum [known]:
  fixes a b
  shows "neg (a  \<oplus> c) = (neg a)  \<oplus> (neg c)"
proof -
  show ?thesis using known by metis
qed

lemma lt_add_const [known]:
  fixes a b c
  assumes "a lt b"
  shows  "(a  \<oplus> c) lt (b  \<oplus> c)"
proof -
  show ?thesis using assms known 
    by (smt (verit))
qed

lemma lt_transitive [known]: 
  fixes a b c
  assumes "a lt b" and "b lt c"
  shows "a lt c"
proof -
  show ?thesis using assms known
  by (smt (verit))
qed

definition NN where "NN = P \<union> {Z}"
declare NN_def [known]

lemma NN_sum_closure [known]:
  fixes a b
  assumes "a \<in>  NN"
  assumes "b \<in>  NN"
  assumes "b \<in>  NN"
  shows "a  \<oplus> b  \<in>  NN"
proof (cases "a = Z")
  case True
  show ?thesis using known assms True by metis
next
  case False
  show ?thesis using known assms False
  by (metis (no_types, lifting) UnE UnI1 singleton_iff)
qed

lemma NN_ge [known]:
  fixes a b
  assumes "a ge b"
  shows "a  \<ominus> b  \<in>  NN"
proof -
  show ?thesis using known assms
    by (metis UnI1 UnI2 insertCI)
qed

lemma ge_NN [known]:
  fixes a b
  assumes "a  \<ominus> b  \<in>  NN"
  shows "a ge b"
proof -
  show ?thesis using known assms 
    by (smt (verit, best) Un_commute insert_iff insert_is_Un)
qed

lemma ge_or_lt [known]:
  fixes a b
  shows "(a ge b) \<or> (a lt b)"
proof -
  show ?thesis using known by meson
qed


lemma le_transitive [known]: 
  fixes a b c
  assumes "a le  b" and "b le  c"
  shows "a le  c"
proof -
  show ?thesis using assms known
  by (smt (verit, best))
 
qed

lemma neg_prod_pos [known]:
  fixes a b
  assumes "a lt Z" and "b lt Z"
  shows " (a  \<odot> b) gt Z"
proof -
  show ?thesis using assms known  by (smt (verit))
qed

lemma square_pos [known]:
  fixes b
  assumes "b \<noteq> Z"
  shows " (b \<odot> b) gt  Z"
proof -
  show ?thesis using assms known 
    by (metis (full_types))
qed

lemma one_pos [known]:
  shows "U gt  Z"
proof -
  show ?thesis using known by metis
qed


definition abs  where
"abs a  \<equiv> (if (a ge Z) then a else neg a)"
declare abs_def [known]
(* Tiny lemmas *)
lemma nnabs [known]:
  fixes a::r
  assumes "a ge Z"
  shows "(abs a) = a"
proof -
  show ?thesis using known assms by metis
qed

lemma gt_weaken [known]:
  fixes a::r
  assumes "a gt Z"
  shows "a ge Z"
proof -
  show ?thesis using known assms by metis
qed

lemma ge_ne [known]:
  fixes a::r
  assumes "a ge b" and "a \<noteq> b"
  shows "a gt b"
proof -
  show ?thesis using known assms by metis
qed

lemma le_ne [known]:
  fixes a::r
  assumes "a le b" and "a \<noteq> b"
  shows "a lt b"
proof -
  show ?thesis using known assms by metis
qed

lemma le_sum_const [known]:
  fixes a b c
  assumes "a le b" 
  shows "(a \<oplus> c) le (b \<oplus> c)"
proof -
  show ?thesis using known assms by metis
qed

lemma le_sum [known]:
  fixes a b c d
  assumes "a le c" and "b le d"
  shows "(a \<oplus> b) le (c \<oplus> d)"
proof -
  have 1: "(a \<oplus> b) le (c \<oplus> b)" using known assms(1) le_sum_const by meson
  have 2: "(b \<oplus> c) le (d \<oplus> c)" using known assms(2)  by meson
  have 3: "(c \<oplus> b) le (c \<oplus> d)" using known 2 by metis
  show ?thesis using 1 3 known by metis
qed

lemma equals_add_equals [known]: 
  fixes a::r and b and c
  assumes "a = b"
  shows "a \<oplus> c = b \<oplus> c"
proof -
  show ?thesis using known assms by blast
qed

lemma self_diff [known]:
  fixes a::r 
  shows "a \<ominus> a = Z"
proof -
  show ?thesis using known by metis
qed

lemma lt_not_eq_h [known]:
  fixes a::r and b
  assumes "a lt b" and "a = b"
  shows "False"
proof - 
  show ?thesis using known assms by metis
qed

lemma lt_not_eq [known]:
  fixes a::r and b
  assumes "a lt b" 
  shows "a \<noteq>  b"
proof - 
  show ?thesis using known assms by metis
qed

lemma lt_not_ge [known]:
  fixes a::r and b
  assumes "a lt b"
  shows "\<not>( a ge b)"
proof - 
  show ?thesis using known assms by metis
qed

lemma posneg [known]:
  fixes a::r
  assumes "a gt Z"
  shows "(neg a) lt Z"
proof -
  show ?thesis using known assms by metis
qed

lemma negpos [known]:
  fixes a::r
  assumes "a lt Z"
  shows "(neg a) gt Z"
proof -
  show ?thesis using known assms by metis
qed

(* ==== a long-winded triangle-ineq proof*)
lemma ti_z [known]:
  fixes a
  assumes "a = Z"
  shows "(abs ( neg a)) =  (abs a)"
proof -
  show ?thesis using known assms by metis
qed

lemma abs_zero [known]:
  shows "abs Z = Z"
proof -
  show ?thesis using known by metis
qed

lemma abs_pos [known]:
  fixes a
  assumes "a \<in> P"
  shows "(abs a) = a"
proof -
  show ?thesis using known assms by metis
qed

lemma abs_NN [known]:
  fixes a
  assumes "a ge Z"
  shows "(abs a) = a"
proof (cases "a = Z")
  case True
  show ?thesis using known assms True by meson
next
  case False
  show ?thesis using known assms False by meson
qed


lemma abs_neg [known]:
  fixes a
  assumes "\<not> (a \<in> P)" and "\<not> (a = Z)" 
  shows "(abs a) = neg a"
proof -
  show ?thesis using known assms  by  meson
qed

lemma abs_neg2 [known]:
  fixes a
  assumes "a le Z" 
  shows "(abs a) = neg a"
proof (cases "a = Z")
  case True
  show ?thesis using known assms True by argo
next
  case False
  show ?thesis using known assms False by metis
qed

lemma ti_x1 [known]:
  fixes a
  assumes "a gt Z"
  shows "(abs ( neg a)) =  (abs a)"
proof -
  show ?thesis using known assms by metis
qed

lemma ti_x2 [known]:
  fixes a
  assumes "a lt Z"
  shows "(abs ( neg a)) =  (abs a)"
proof - 
  show ?thesis using known assms by metis
qed

lemma tix3 [known]:
  fixes a
  shows "(abs ( neg a)) =  (abs a)"
proof -
  show ?thesis using known by metis
qed

lemma ti_y1 [known]:
  fixes a
  shows "a le (abs a)"
proof -
  show ?thesis using known by metis
qed

theorem triangle_inequality [known]:
  fixes x y
  shows "(abs (x \<oplus> yb)) le  ((abs x)  \<oplus> (abs y))"
proof -
  presume A: "\<lbrakk>x gt Z; y gt Z\<rbrakk> \<Longrightarrow> (abs (x \<oplus> y)) le  ((abs x)  \<oplus> (abs y))"
  show ?thesis using A 
  proof -
    lots of steps here
    sorry
  qed 
next
  show "\<lbrakk>x gt Z; y gt Z\<rbrakk> \<Longrightarrow> (abs (x \<oplus> y)) le  ((abs x)  \<oplus> (abs y))"
  proof -
     lots of steps here too
  qed
qed


lemma 
  fixes x::real and y::real
  shows "x^2 + x*y + y^2 \<ge> 0"
proof -
  presume A: "\<lbrakk>x gt Z, y gt Z\<rbrakk>\<Longrightarrow> 0 \<le> 4*x^2 + 4*x*y + 4*y^2"
  show ?thesis using A by auto
next
  have 1: "4*x^2 +4* x*y + 4*y^2 = (4*x^2 + 4*x*y + (y^2)) + 3*y^2" by simp
  have 2: "(4*x^2 + 4*x*y + y^2) = (2*x + y)^2" by (simp add: power2_sum) 
  have 3: "4*x^2 +4* x*y + 4*y^2 = (2*x + y)^2 + 3*y^2" using 1 2 by simp
  have 4: "0 \<le> (2*x + y)^2 + 3*y^2" using 3 twoSquares [of "(2*x +y)" "y" ] by simp
  show "0 \<le> 4*x^2 + 4*x*y + 4*y^2"  using 4 3 by presburger
qed

lemma ti_lhsNN [known]:
  fixes a and b
  assumes "(a \<oplus> b) ge Z"
  shows "(abs (a \<oplus> b)) le  ((abs a)  \<oplus> (abs b))"
proof -
  show ?thesis using known assms by metis
qed

lemma ti_lhs_negative [known]:
  fixes a and b
  assumes "(a \<oplus> b) lt Z"
  shows "(abs (a \<oplus> b)) le  ((abs a)  \<oplus> (abs b))"
proof -
  show ?thesis using known assms by (smt (verit, ccfv_SIG))
qed

theorem triangle_inequality [known]:   
  fixes a and b
  shows "(abs (a \<oplus> b)) le  ((abs a)  \<oplus> (abs b))"
proof -
  show ?thesis using known  by metis
qed
