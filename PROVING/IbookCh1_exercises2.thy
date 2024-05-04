(* TO BE RENAMED *)
(* Exercise solutions for chapter 2: take the Spivak work from 
Chapter 1 and add markers like [simps] to make the proofs
easier; try to turn everything into a 1-liner 
*)

(* Chapter 2 exercises: re-do the Spivak exercises from Chapter 1,
but this time condesing things as much as possible. I've removed the quoted text from Spivak
and my comments on it for the most part. *)

theory IbookCh1_exercises2
  imports Main
begin
(* declare [[show_types]] *)

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

lemma plus_assoc:
  fixes a::r and b::r and c::r
  shows "(a \<oplus> b) \<oplus> c =  a \<oplus> (b \<oplus> c)"
  sorry


lemma ex1: 
  fixes a::r and b::r and c::r and d::r
  shows "(a \<oplus> (b \<oplus> c)) \<oplus> d =  a \<oplus> ((b \<oplus> c) \<oplus> d)"
   using plus_assoc by auto

(* added [simp] so that the simplifier knows about this, and we never need to mention it again *)
lemma additive_ident [simp]:
  fixes a::r
  shows "a \<oplus> Z = a" and "Z \<oplus> a = a"
  sorry

lemma  negation [simp]: 
  fixes a::r
  shows "a \<oplus> (neg a) =  Z"
  and  "(neg a) \<oplus> a =  Z"
  sorry

theorem  ex2 [simp]: 
  fixes a::r and x
  assumes "a \<oplus> x =  a"
  shows "x =  Z"

proof -
  have 0: "(neg a) \<oplus> (a \<oplus> x) = (neg a) \<oplus> a" using [[simp_trace]] using assms  by (auto simp del:negation)
  show ?thesis   using [[simp_trace]] using 0  plus_assoc  additive_ident negation by metis
qed

definition diff:: "r \<Rightarrow> r \<Rightarrow> r" where
"diff a b \<equiv> (a \<oplus> (neg b))"

notation diff  (infix "\<ominus>" 80) 

lemma ex3: 
  fixes x::r and a and b
  assumes "x \<oplus> a = b"
  shows "x = b \<ominus> a"
proof -
  show ?thesis unfolding diff_def using assms plus_assoc by auto
qed

lemma plus_comm:
  fixes a::r and b::r 
  shows "(a \<oplus> b) =  (b \<oplus> a)"
  sorry

lemma mul_assoc: 
  fixes a::r and b::r and c::r
  shows "((a \<odot> b) \<odot> c) =  (a \<odot> (b \<odot> c))"
  sorry

lemma mul_ident [simp]:  
  fixes a::r
  shows "a \<odot> U =  a" and "U \<odot> a =  a" and "Z \<noteq> U"
  sorry

lemma inversion [simp] : 
  fixes a::r
  assumes "a \<noteq> Z"
  shows "a \<odot> (reciprocal a) =  U" and "(reciprocal a) \<odot>  a =  U"
  sorry

lemma mul_commute:
  fixes a::r and b::r 
  shows "(a \<odot> b) =  (b \<odot> a)"
  sorry

lemma distrib:
  fixes a::r and b::r and c::r
  shows "(a \<odot> (b \<oplus> c)) =  ((a \<odot> b) \<oplus> (a \<odot> c))"
  sorry

lemma ex6: 
  fixes a::r and b and c
  assumes "a \<odot> b = a \<odot> c" and "a \<noteq> Z"
  shows "b = c"
proof -
  have 2: "((reciprocal a) \<odot> a) \<odot> b = ((reciprocal a) \<odot> a)  \<odot> c" 
    using assms mul_assoc by (auto simp del:inversion)
  show ?thesis using  2 assms  mul_ident by auto
qed

lemma ex7a  :
  fixes a::r
  shows "a \<odot> Z = Z"
proof -
  show ?thesis using [[metis_trace]]
    by (metis distrib additive_ident(2) ex2) 
qed

lemma ex7:
  fixes a::r and b
  assumes "a \<odot> b = Z" 
  shows "(a = Z) \<or> (b = Z)"
  by (metis assms ex6 ex7a)

lemma mulZ [simp]: 
  fixes a
  shows "(a  \<odot> Z) = Z" and "(Z  \<odot> a) = Z"
proof -
  show "(a  \<odot> Z) = Z" using  ex7a by auto
  show "(Z  \<odot> a) = Z" using  ex7a mul_commute by fastforce
qed

lemma unique_neg:
  fixes a b
  assumes "u  \<oplus> x = Z"
  shows "x = neg u"
proof -
  show ?thesis
    by (metis additive_ident(2) assms diff_def ex3) 
qed

lemma move_neg: 
  fixes a b
  shows "(neg a)  \<odot> b = neg(a  \<odot> b)"
proof -
  show ?thesis
    by (metis distrib additive_ident(2) diff_def ex3 mul_commute) 
qed

lemma neg_product: 
  fixes a b
  shows "(neg a)  \<odot> (neg b) = a  \<odot> b"
  
  proof -
    have "\<forall>r. neg (neg r) = r"
      by (metis (no_types) ex3 negation(1) negation(2))
    then show ?thesis
      using move_neg mul_commute by auto
  qed 
  
(* A few more warmup lemmas *)
  thm ex2 [where a = Z]

lemma negZ [simp]:
  shows "neg Z = Z"
(*hint: Z + (neg Z) = Z; does a prior lemma then help? *)
proof -
  have 0: "Z  \<oplus> (neg Z) = Z" using negation by auto
  show ?thesis using [[simp_trace]]  0 ex2 [where a = Z]  by blast
qed

lemma subtractZ:
  shows "a \<ominus> Z = a  \<oplus> (neg Z)"
proof -
  show ?thesis using diff_def by auto
qed

lemma subtractZ2:
  shows "a \<ominus> Z = a  \<oplus> Z"
proof -
  show ?thesis using subtractZ negZ by auto
qed

lemma subtractZ3 [simp]:
  shows "a \<ominus> Z = a"
proof -
  show ?thesis using subtractZ2 additive_ident by auto
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
 
lemma gtP1:
  assumes "gt a Z"
  shows "a \<in> P"
proof -
  show ?thesis using assms gt_def by auto  
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
  shows "(a \<ominus> b = Z \<and> \<not>( a \<ominus> b \<in> P \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
(a \<ominus> b \<in> P \<and> \<not>( a \<ominus> b = Z \<or>  (neg (a \<ominus> b)) \<in> P)) \<or>
((neg (a \<ominus> b)) \<in> P \<and> \<not>( a \<ominus> b = Z \<or> a \<ominus> b \<in> P))"
proof -
  show ?thesis using trichotomy by auto
qed

lemma help1: 
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

lemma help2: 
  fixes a b
  assumes "a \<ominus> b \<in> P"
  shows "gt a b"
proof -
  show ?thesis using assms gt_def by auto
qed

lemma negsub:
  fixes a b
  shows "b \<ominus> a = neg(a \<ominus> b)"
proof - 
  show ?thesis unfolding diff_def
    by (metis diff_def ex3 plus_comm) 
qed

lemma help3: 
  fixes a b
  assumes "(neg (a \<ominus> b)) \<in> P"
  shows "gt b a"
proof -
  have 0: "neg(a \<ominus> b) = b \<ominus> a" using  negsub by metis
  have 1: "b \<ominus> a \<in> P" using assms 0 by auto
  show ?thesis using 1 gt_def by auto 
qed


lemma help3b: 
  fixes a b
  assumes "gt b a"
  shows "(neg (a \<ominus> b)) \<in> P"
proof -
  have 0: "b \<ominus> a \<in> P" using assms gt_def by auto
  have 1: "neg(a \<ominus> b) = b \<ominus> a" using  negsub by metis
  have 2: "neg(a \<ominus> b) \<in> P" using 0 1  by auto
  show ?thesis using 2 gt_def by auto 
qed

lemma help3c:
  fixes a b
  shows "gt b a = ((neg (a \<ominus> b)) \<in> P)"
proof -
  show ?thesis using help3 help3b by auto
qed

lemma trichotomy3:
  fixes a b
  assumes "h1 = (a = b)" and "h2 = (gt a b)" and "h3 = (gt b a)"
  shows "(h1 \<and> \<not>( h2 \<or> h3)) \<or> 
(h2 \<and> \<not>( h1 \<or> h3)) \<or> 
(h3 \<and> \<not>( h1 \<or> h2))" using gt_def assms
  by (metis help1 help3c trichotomy2) 

lemma neg_sum:
  fixes a b
  shows "neg (a  \<oplus> c) = (neg a)  \<oplus> (neg c)"
  by (metis diff_def ex3 plus_comm)

thm plus_comm

lemma slightly_more_interesting:
  fixes a b c
  assumes "lt a b"
  shows "lt (a  \<oplus> c) (b  \<oplus> c)"
proof -
  have 4: "(b  \<oplus> ((neg a)  \<oplus> c))  \<oplus> (neg c) \<in> P" 
    using   assms lt_def gt_def diff_def negation additive_ident plus_assoc by auto
  have 6: "((b  \<oplus> c)  \<oplus> (neg a))  \<oplus> (neg c) \<in> P" 
    using 4 plus_comm plus_assoc by auto
  show ?thesis using 6 plus_assoc neg_sum diff_def diff_def  lt_def gt_def by auto
qed

thm plus_assoc
lemma almost_done: 
  fixes a b c
  assumes "lt a b" and "lt b c"
  shows "lt a  c"
proof -
  have 3:"(c  \<oplus> (neg b))  \<oplus> (b   \<oplus> (neg a)) \<in> P" 
    unfolding diff_def using assms lt_def gt_def additive_closure  diff_def by auto
  have 4:"c  \<oplus> ((neg b)  \<oplus> (b   \<oplus> (neg a))) \<in> P" using 3 plus_assoc by auto
  have 5:"c  \<oplus> (((neg b)  \<oplus> b)   \<oplus> (neg a)) \<in> P" 
    using 4 plus_assoc [where a = "neg b" and c = "neg a"] by metis
  have 6:"c  \<oplus>  (neg a) \<in> P" using 5 by auto
  show ?thesis unfolding lt_def gt_def diff_def
     using "6" by force  
qed

definition NN where "NN = P \<union> {Z}"

lemma NN_closure:
  fixes a b
  assumes "a \<in>  NN"
  assumes "b \<in>  NN"
  assumes "b \<in>  NN"
  shows "a  \<oplus> b  \<in>  NN"
  by (metis NN_def Un_iff additive_closure additive_ident(1) assms(1) assms(2) plus_comm singletonD)

lemma NN_ge:
  fixes a b
  assumes "ge a b"
  shows "a  \<ominus> b  \<in>  NN"
proof -
  show ?thesis
    using NN_def assms diff_def ge_def by auto
qed

lemma ge_NN:
  fixes a b
  assumes "a  \<ominus> b  \<in>  NN"
  shows "ge a b"
proof -              
  show ?thesis
    by (metis NN_def UnE assms ge_def help1 singleton_iff)
qed

lemma almost_done_le: 
  fixes a b c
  assumes "le a b" and "le b c"
  shows "le a  c"
proof -
  show ?thesis
    by (smt (verit) additive_closure assms(1) assms(2) diff_def ex3 ge_def le_def negation(2) plus_assoc) 
qed

lemma neg_prod_pos:
  fixes a b
  assumes "lt a Z" and "lt b Z"
  shows "gt (a  \<odot> b) Z"
proof -
  show ?thesis 
    by (metis assms(1) assms(2) ex3 gtP2 gt_def lt_def multiplicative_closure neg_product negation(2)) 
qed

lemma square_pos:
  fixes b
  assumes "b \<noteq> Z"
  shows "gt (b \<odot> b)  Z"
proof -
  show ?thesis
    by (metis additive_ident(2) assms diff_def gtP2 gt_def lt_def multiplicative_closure neg_prod_pos trichotomy)
qed

lemma one_pos:
  shows "gt U  Z"
  using neg_prod_pos [where a = U and b = U] by auto 

definition abs  where
"abs a  \<equiv> (if gt a Z then a else neg a)"

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
  have 2: "ge  (a \<oplus> b) Z" using assms ge_def gt_def additive_closure by auto
  have 3: "Nab =  (a \<oplus> b)" using abs_def 2 ge_def gt_def assms negZ by auto
  have 4: "Nab =  (Na \<oplus> Nb)" using 3 0 1 by auto
  have 5: "le Nab (Na \<oplus> Nb)" using 4 le_def ge_def by auto
  show ?thesis using 5 by auto
qed
thm unique_neg

lemma negneg [simp]:
  fixes a::r 
  shows "neg (neg a) = a"
proof -
  have 0: "(neg a)  \<oplus> a = Z" using unique_neg negation by auto
  have 1: "neg (neg a) = a" using 0 unique_neg [where u = "(neg a)"] by fastforce
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
  have 0: "Na = neg a" using abs_def assms  ge_def gt_def lt_def negZ 
    by (meson help3b trichotomy)
  have 1: "Nb = neg b" using  abs_def assms  ge_def gt_def lt_def negZ  by (meson help3b trichotomy)
  have 2: "lt  (a \<oplus> b) Z" using assms ge_def gt_def lt_def additive_closure
    by (metis additive_ident(1) diff_def ex3 negsub)
  have 3: "Nab = neg (a \<oplus> b)" using abs_def 2 ge_def gt_def lt_def assms negZ 
    using trichotomy3 by fastforce
  have 4: "neg (a \<oplus> b) = (neg a) \<oplus> (neg b)"  using neg_sum by auto 
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
  have 1: "Nb = neg b" using  abs_def assms  ge_def gt_def lt_def negZ 
    using trichotomy3 by fastforce
  have 2: "gt  (a \<oplus> b) Z" using assms by auto 
  have 3: "Nab = (a \<oplus> b)" using abs_def 2 ge_def gt_def lt_def assms negZ 
    using trichotomy3 by fastforce
  have 4: "lt b (neg b)" using assms lt_def
    by (simp add: additive_closure  diff_def gt_def)
  have 5: "lt (b \<oplus> a)  ((neg b) \<oplus> a)" using 4 assms le_def lt_def gt_def slightly_more_interesting by auto
  have 6: "lt (a \<oplus> b)  (a \<oplus> (neg b))" using 5 plus_comm by auto
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
  have 1: "Nb = neg b" using  abs_def assms  ge_def gt_def lt_def negZ 
    using trichotomy3 by fastforce
  have 2: "le  (a \<oplus> b) Z" using assms by auto 
  have 3: "Nab = ((neg a)  \<ominus>  b)" using diff_def abs_def 2 ge_def gt_def lt_def assms negZ 
    trichotomy3   by (metis le_def neg_sum)
  have 4: "le (neg a) Z" using assms(5) le_def 
    by (metis ge_def   negsub subtractZ3)
  have 5: "le  Z a" using assms(5) le_def by auto
  have 6: "le (neg a) a"
    using "4" "5" almost_done_le by blast  
  have 7: "le ((neg a)  \<ominus> b)  (a  \<ominus> b)" using 6 assms le_def lt_def gt_def diff_def ge_def 
      slightly_more_interesting by auto
  have 8: "le ((neg a)  \<ominus> b)  (a \<oplus> (neg b))" using 7 plus_comm diff_def by auto
  have 9: "le Nab (Na \<oplus> Nb)" using 8 le_def 3 0 1 by auto
  have 10: "le Nab (Na \<oplus> Nb)" using 9 le_def by auto
  then show ?thesis using 10 by auto 
qed

lemma ge_lt:
  fixes b
  assumes "(\<not> ge b Z)"
  shows "lt b Z"
proof -
  have 0:  "\<not>((b \<ominus> Z)  \<in> P) \<and> (b \<noteq> Z)" using assms ge_def by simp
  have 1:  "\<not>((b \<ominus> Z)  \<in> P)" using 0 by simp
  have 2:  "\<not>(b  \<in> P)" using 1 subtractZ3 by auto
  have 3: " (neg b) \<in> P" using 0 2 trichotomy by auto
  have 4: " (neg b) = Z \<ominus> b"  using diff_def additive_ident by auto
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
  have 3: " (neg b) \<in> P \<or> b = Z " using 0 2 trichotomy by auto
  have 4: " (neg b) = Z \<ominus> b"  using diff_def additive_ident by auto
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
  have 3:  "\<not>( b = Z \<and> ((neg b)  \<in> P))" using 2 0 negation diff_def by auto
  have 4: "(b = Z \<and> \<not>( b \<in> P \<or>  (neg b) \<in> P)) \<or>
  (b \<in> P \<and> \<not>( b = Z \<or>  (neg b) \<in> P)) \<or>
((neg b) \<in> P \<and> \<not>( b = Z \<or> b \<in> P))" using trichotomy by auto
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
  have 2: "Z \<ominus> b = Z \<or> (neg (Z \<ominus> b)) \<in> P" using 1 trichotomy ge_def by auto
  have 3: "Z \<ominus> b = Z \<or> (neg (Z \<ominus> b)) \<in> P" using 2 diff_def additive_ident by auto
  have 4: "Z \<oplus>neg  b = Z \<or> (neg (Z \<ominus> b)) \<in> P" using 3 diff_def additive_ident by auto
  have 5: "neg  b = Z \<or> (neg (Z \<ominus> b)) \<in> P" using 4 diff_def additive_ident by auto
  have 6: "neg (neg  b) = neg Z \<or> (neg (Z \<ominus> b)) \<in> P" using 5 negation 
    by fastforce
  have 7: "  b = neg Z \<or> (neg (Z \<ominus> b)) \<in> P" using 6 negneg by auto
  have 8: "  b = Z \<or> (neg (Z \<ominus> b)) \<in> P" using 7 negZ by auto
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
      by (metis assms(1) assms(2) assms(3) ge_lt gt_le plus_comm ti3 ti4)      
  next
    case False
    have bNeg:  "\<not>(ge b Z)" using False by auto
    then show ?thesis using aNeg bNeg
      by (simp add: assms(1) assms(2) assms(3) ge_lt ti2) 
  qed
qed

end
