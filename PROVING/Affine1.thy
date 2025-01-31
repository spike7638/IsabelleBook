theory Affine1 (* 1/29/2025 -- about 500 lines shorter than prior version *)
  imports Complex_Main 
begin

locale affine_plane_data =
  fixes Points :: "'p set" and Lines :: "'l set" and meets :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes join:: "'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel:: "'l \<Rightarrow> 'p \<Rightarrow> 'l"
begin
(*
  fun parallel :: "'l \<Rightarrow> 'l \<Rightarrow> bool" (infix "||" 50) where
  "l || m = (if (l \<in> Lines \<and> m \<in> Lines) 
  then l = m \<or> \<not> (\<exists> P. P \<in> Points \<and> meets P l \<and> meets P m) else undefined)"
*)
definition parallel::"'l \<Rightarrow> 'l \<Rightarrow> bool"  (infix "||" 50)  where
  "parallel l m = (if (l \<in> Lines \<and> m \<in> Lines) 
  then l = m \<or> \<not> (\<exists> P. P \<in> Points \<and> meets P l \<and> meets P m) else undefined)"
fun collinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
    where "collinear A B C = (if A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
  then (\<exists> l. l \<in> Lines \<and> meets A l \<and> meets B l \<and> meets C l) else undefined)"
end

locale affine_plane =
    affine_plane_data  +
    assumes
    a1a: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> join P Q \<in> Lines \<and> meets P (join P Q)  \<and> meets Q (join P Q)" and
    a1b: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points; meets P m; meets Q m\<rbrakk> \<Longrightarrow> m = join P Q" and
    a2: "\<lbrakk>\<not> meets P l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> find_parallel l P \<in> Lines \<and> ( find_parallel l P) || l \<and> meets P (find_parallel l P)" and
    a3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)"
begin

lemma join_symmetric: 
  fixes P Q
  assumes "P \<in> Points"
  assumes "Q \<in> Points"
  assumes "P \<noteq> Q" 
  shows "join P Q = join Q P" 
proof -
  have 2: "meets P (join Q P)" using assms a1a by auto
  have 3: "meets Q (join Q P)" using assms a1a by auto
  have "join Q P = join P Q" using assms 2 3  a1b by blast
  then show ?thesis by auto
qed

fun (in affine_plane_data) liesOn :: "'p \<Rightarrow> 'l \<Rightarrow> bool" (infix "liesOn" 50) where
  "P liesOn m = (if P  \<in> Points \<and> (m \<in> Lines) then meets P m  else undefined)"

fun  (in affine_plane_data) contains :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "contains" 50) where
  "m contains P = (P liesOn m)"

theorem join_containsL:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "P liesOn (join P Q)"
proof -
  have 0: "meets P (join P Q)" using a1a assms by blast
  have 1: "(join P Q)  \<in> Lines" using a1a assms by blast
  show ?thesis by (simp add: "0" "1" assms)
qed                                                                

theorem join_containsL2:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "meets P (join P Q)"
proof -
  show ?thesis using a1a assms by blast
qed                                                                

theorem join_containsR:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "Q liesOn (join P Q)"
proof -
  have 0: "meets Q (join P Q)" using a1a assms by blast
  have 1: "(join P Q)  \<in> Lines" using a1a assms by blast
  show ?thesis by (simp add: "0" "1" assms)
qed                                                                

theorem join_containsR2:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "meets Q (join P Q)"
proof -
 show ?thesis  using a1a assms by blast
qed                                                                

theorem join_symmetric0:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"
  shows "join P Q = join Q P"
proof -
  have 0: "meets Q (join Q P)" using "join_containsL2" assms by simp
  have 1: "meets P (join Q P)" using "join_containsR2" assms by simp
  have 2: "(join Q P) = (join P Q)" using "0" "1" a1b assms by blast 
  thus ?thesis by simp
qed

theorem contains_implies_liesOn:
  fixes P m
  assumes "P  \<in> Points"
  assumes "m  \<in> Lines"
  assumes "m contains P"
  shows "P liesOn m"
proof -
  have 0: "m contains P" using assms by simp
  have 1: "P liesOn m" using "0" "contains_def" by simp
  thus ?thesis by simp
qed

theorem liesOn_implies_contains:
  fixes P m
  assumes "P  \<in> Points"
  assumes "m  \<in> Lines"
  assumes "P liesOn m"
  shows "m contains P"
proof -
  have 0: "m contains P" using assms by simp
  thus ?thesis by auto
qed

(* Let's show that the 4-point affine plane is an affine plane. That entails creating Point, Lines, contains, and join. 
*)

datatype a4pt = Pa | Qa | Ra | Sa
definition  "A4Points = {Pa, Qa, Ra, Sa}"
definition "A4PQ = {Pa, Qa}"
definition "A4PR = {Pa, Ra}"
definition "A4PS = {Pa, Sa}"
definition "A4QR = {Qa, Ra}"
definition "A4QS = {Qa, Sa}"
definition "A4RS = {Ra, Sa}"

definition "A4Lines = {A4PQ, A4PR, A4PS, A4QR, A4QS, A4RS}"

fun  A4join::"a4pt \<Rightarrow> a4pt \<Rightarrow> a4pt set"  where 
"A4join x y = (if (x = y) then undefined else {x, y})"


fun A4meets::"a4pt \<Rightarrow> a4pt set \<Rightarrow> bool" where
"A4meets x m = ((m \<in> A4Lines) \<and> (x \<in> m))"

fun A4complement::"a4pt set \<Rightarrow> a4pt set" where
"A4complement n = (if n = A4PQ then A4RS else 
(if n = A4RS then A4PQ else 
(if n = A4PR then A4QS else
(if n = A4QS then A4PR else 
(if n = A4PS then A4QR else 
(if n = A4QR then A4PS else 
undefined))))))"

fun A4find_parallel::"a4pt set \<Rightarrow> a4pt \<Rightarrow> a4pt set"  where
"A4find_parallel m T = (if T \<in> m then m else (A4complement m))"

thm A4meets.simps
thm A4join.simps 
thm A4Points_def

lemma all_pairs:
  fixes P::a4pt and Q::a4pt
  assumes "P \<noteq> Q" 
  shows "{P, Q} \<in> A4Lines"
  by (metis (full_types) A4Lines_def A4PQ_def A4PR_def A4PS_def 
      A4QR_def A4QS_def A4RS_def a4pt.exhaust assms 
      insert_commute insert_subset subset_insertI)

lemma all_joins_are_lines:
  fixes P Q
  assumes   "P \<noteq> Q" and
  "P \<in> A4Points"  and" Q \<in> A4Points"
shows "A4join P Q \<in> A4Lines"
proof -
  show ?thesis by (simp add: all_pairs assms(1))
qed

theorem PinPQ1:
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and" Q \<in> A4Points"
shows "P \<in> A4join P Q"
proof -
  show ?thesis by (simp add: assms(1))
qed

theorem QinPQ1:
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and" Q \<in> A4Points"
shows "Q \<in> A4join P Q"
proof -
  show ?thesis by (simp add: assms(1))
qed

theorem
  fixes P Q
  assumes   "P \<noteq> Q" and
  "P \<in> A4Points"  and "Q \<in> A4Points"
shows "A4meets P (A4join P Q)"
proof -
  show ?thesis using assms A4meets.elims A4join.simps all_pairs by auto
qed

theorem
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and " Q \<in> A4Points"
shows "A4meets Q (A4join P Q)"
proof -
  show ?thesis using assms A4meets.elims A4join.simps all_pairs by auto
qed

lemma not_four_and:
  fixes p1 p2 p3 p4
  assumes "\<not> (p1 \<and> p2 \<and> p3 \<and> p4)"
  shows   "(\<not> p1) \<or> (\<not> p2) \<or> (\<not> p3) \<or> (\<not> p4)"
proof -
  show ?thesis using assms by blast
qed

theorem A4affine_plane_a3_lemma: 
  shows "Pa \<in> A4Points \<and>
       Qa \<in> A4Points \<and>
       Ra \<in> A4Points" and 
       "Pa \<noteq> Qa \<and>
       Pa \<noteq> Ra \<and>
       Qa \<noteq> Ra" and 
       "\<not> affine_plane_data.collinear
           A4Points
           A4Lines
           A4meets Pa Qa Ra"
proof -
  show P1: "Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points" using A4Points_def by blast
  show P2: "Pa \<noteq> Qa \<and> Pa \<noteq> Ra \<and> Qa \<noteq> Ra" by auto
  show P3: "\<not> affine_plane_data.collinear
           A4Points
           A4Lines
           A4meets Pa Qa Ra"
  proof (rule ccontr)
    assume cHyp: "\<not>\<not>affine_plane_data.collinear
           A4Points
           A4Lines
           A4meets Pa Qa Ra"
    have 2: "(if Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points  then (\<exists> l. l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l \<and> A4meets Ra l) else undefined)"
      using cHyp by (simp add: affine_plane_data.collinear.simps)
    then obtain n where 3:"n \<in> A4Lines \<and> A4meets Pa n \<and> A4meets Qa n \<and> A4meets Ra n" using A4Points_def A4Lines_def P1 by auto
    have cP: "(n = {Pa, Qa}) \<or> (n = {Pa, Ra}) \<or> (n = {Pa, Sa})"  
      by (metis (full_types) "3" A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4meets.simps P2 empty_iff insert_iff)
    have cQ: "(n = {Pa, Qa}) \<or> (n = {Qa, Ra}) \<or> (n = {Qa, Sa})"  
      by (metis (full_types) "3" A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4meets.simps P2 empty_iff insert_iff)
    have cPQ: "n = {Pa, Qa}" using cP cQ by blast
    have ncR: "\<not> A4meets Ra n" using A4meets.simps cPQ by auto
    show f: False using ncR 3 by auto
  qed
qed

theorem A4affine_plane_a3: " \<exists>P Q R.
       P \<in> A4Points \<and>
       Q \<in> A4Points \<and>
       R \<in> A4Points \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> affine_plane_data.collinear
           A4Points
           A4Lines
           A4meets P Q R" 
proof -
  show ?thesis  using A4affine_plane_a3_lemma(1) A4affine_plane_a3_lemma(3) by blast
qed

theorem A4affine_plane_a1a: 
  fixes P Q
  assumes " P \<noteq> Q" and "P \<in> A4Points" and " Q \<in> A4Points" 
  shows "A4join P Q \<in> A4Lines" and "A4meets P (A4join P Q)" and "A4meets Q (A4join P Q)"
proof -
  show "A4join P Q \<in> A4Lines" using all_joins_are_lines using assms by blast
next
  show "A4meets P (A4join P Q)" using A4meets.simps A4join.simps A4Lines_def assms by (simp add: all_pairs)
next
  show "A4meets Q (A4join P Q)" using A4meets.simps A4join.simps A4Lines_def assms by (simp add: all_pairs)
qed

theorem A4affine_plane_a1b:  
  fixes P Q
  assumes 
    "P \<noteq> Q" and 
    "P \<in> A4Points" and  "Q \<in> A4Points" and
    "A4meets P m" and "A4meets Q m"
  shows "m = A4join P Q"
proof -
  show ?thesis by (smt (verit, best) A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4meets.elims(2) affine_plane.A4join.simps affine_plane_axioms assms(1) assms(4) assms(5) insertE insert_commute singleton_iff)
qed (* replaced a 250-line proof! *)

lemma A4line_complement:
  fixes l
  assumes "l \<in> A4Lines"
  shows "A4complement l \<in> A4Lines"
  by (smt (verit, best) A4Lines_def A4complement.simps assms empty_iff insert_iff)

lemma A4complement_parallel_helper: 
  fixes n
  assumes "n \<in> A4Lines"
  shows "n \<inter> (A4complement n) = {}"
proof -
  show ?thesis 
    by (smt (verit) A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def Int_insert_right a4pt.distinct(10) a4pt.distinct(12) a4pt.distinct(2) a4pt.distinct(4) a4pt.distinct(6) a4pt.distinct(8) affine_plane.A4complement.elims affine_plane_axioms assms inf.orderE insertE insert_disjoint(2) insert_inter_insert singletonD singleton_insert_inj_eq)
qed

lemma A4disjoint_parallel:
  fixes n k
  assumes "n \<inter> k = {}" and "n \<in> A4Lines" and "k \<in> A4Lines"
  shows "affine_plane_data.parallel A4Points A4Lines A4meets k n"
proof -
  show ?thesis 
  using affine_plane_data.parallel_def assms(1) assms(2) assms(3) by fastforce
qed

lemma A4complement: 
  fixes n
  assumes "n \<in> A4Lines"
  shows "affine_plane_data.parallel A4Points A4Lines A4meets (A4complement n) n"
proof -
  show ?thesis using A4complement_parallel_helper
    using A4disjoint_parallel A4line_complement assms by auto
qed

theorem A4affine_plane_a2: 
  fixes P l
  assumes "\<not> A4meets P l" 
  assumes "P \<in> A4Points " and "l \<in> A4Lines"
  shows "A4find_parallel l P \<in> A4Lines" and
     "affine_plane_data.parallel A4Points A4Lines A4meets  (A4find_parallel l P) l" and
     "A4meets P (A4find_parallel l P)"
proof -
  show "A4find_parallel l P \<in> A4Lines" using A4line_complement assms(3) by auto
next
  show "affine_plane_data.parallel A4Points A4Lines A4meets  (A4find_parallel l P) l" using A4complement assms by force
next
  show "A4meets P (A4find_parallel l P)" 
  by (smt (verit, del_insts) A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4complement.elims A4find_parallel.elims A4meets.elims(3) Un_iff a4pt.exhaust assms(3) insertI1 insert_is_Un singletonD)
qed

theorem A4affine_plane: "affine_plane A4Points A4Lines A4meets A4join A4find_parallel"
proof standard
  show f1a: "\<And>P Q. P \<noteq> Q \<Longrightarrow> P \<in> A4Points \<Longrightarrow> Q \<in> A4Points \<Longrightarrow> A4join P Q \<in> A4Lines \<and> A4meets P (A4join P Q) \<and> A4meets Q (A4join P Q)" 
    using A4affine_plane_a1a by auto
  show f1b: "\<And>P Q m. P \<noteq> Q \<Longrightarrow> P \<in> A4Points \<Longrightarrow> Q \<in> A4Points \<Longrightarrow> A4meets P m \<Longrightarrow> A4meets Q m \<Longrightarrow> m = A4join P Q"
    using A4affine_plane_a1b by auto    
  show f2: "\<And>P l. \<not> A4meets P l \<Longrightarrow>
           P \<in> A4Points \<Longrightarrow>
           l \<in> A4Lines \<Longrightarrow>
           A4find_parallel l P \<in> A4Lines \<and>
           affine_plane_data.parallel A4Points A4Lines A4meets (A4find_parallel l P) l \<and> A4meets P (A4find_parallel l P)"
    using A4affine_plane_a2 by auto    
  show f3: "\<exists>P Q R. P \<in> A4Points \<and> Q \<in> A4Points \<and> R \<in> A4Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> 
    \<not> affine_plane_data.collinear A4Points A4Lines A4meets P Q R"
    using A4affine_plane_a3   by auto
qed


(* ======================Switch to talking about A2, real affine 2-space =================*)

datatype a2pt = A2Point "real" "real"
datatype a2ln = A2Ordinary "real" "real" 
  | A2Vertical "real"

definition A2Points::"a2pt set"
  where "A2Points \<equiv> (UNIV::a2pt set)"

definition A2Lines::"a2ln set"
  where "A2Lines \<equiv> (UNIV::a2ln set)"

text "Ordinary m b represents the line y = mx+b; Vertical xo is the line x = xo. With this in 
mind, we define the  `meets' operation for this purported plane, using cases for the definition."

text\<open> There's a problem here, though: for A2Ordinary, we have to have the "m" term be nonzero,
so we need to define a set Lines; the set Points is just all a2pts\<close>

fun a2meets :: "a2pt \<Rightarrow> a2ln \<Rightarrow> bool" where
"a2meets (A2Point x y) (A2Ordinary m b) = (y = m*x + b)" |
"a2meets (A2Point x y) (A2Vertical xi) = (x = xi)"

definition a2parallel:: "a2ln  \<Rightarrow> a2ln \<Rightarrow> bool" (infix "a2||" 50)
      where "l a2|| m \<longleftrightarrow> (l = m \<or>  (\<forall> P. (\<not> a2meets P l)  \<or> (\<not>a2meets P m)))"
  
text\<open> Notice that I've written the definition of parallel for the euclidean affine plane
as a forall rather than exists. I think this might make things easier.\<close>


text\<open> To make this work in 2025, I need to provide a join and find_parallel function\<close>
fun a2join :: "a2pt \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"a2join (A2Point x1 y1) (A2Point x2 y2) = (if ((x1 = x2)  \<and> (y1 = y2)) then undefined else if (x1 = x2) then A2Vertical(x1) else 
(A2Ordinary ((y2 - y1)/(x2-x1)) (y1 - x1* (y2 - y1)/(x2-x1))))"

fun a2find_parallel::"a2ln \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"a2find_parallel (A2Ordinary m b) (A2Point x y)  = (A2Ordinary m (y-m*x))" |
"a2find_parallel  (A2Vertical xi) (A2Point x y) = (A2Vertical x)"

text\<open>Now we'll write some small lemmas, basically establishing the three axioms.\<close>

  text\<open>
A note about naming: Everything related to real-affine-2-space will be written with a prefix
``A2''. When we want to state axiom 3 for A2, we'll write ``A2\_a3''. Sometimes we'll need some preliminary
results, and we'll append an ``a'' or ``b'' or ``c'', etc., before stating the main result. \caleb \<close>

(*  "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> join P Q \<in> Lines \<and> meets P (join P Q)  \<and> meets Q (join P Q)" *)

(*

theorem A4affine_plane_a1a: 
  fixes P Q
  assumes " P \<noteq> Q" and "P \<in> A4Points" and " Q \<in> A4Points" 
  shows "A4join P Q \<in> A4Lines" and "A4meets P (A4join P Q)" and "A4meets Q (A4join P Q)"
proof -
  show "A4join P Q \<in> A4Lines" using all_joins_are_lines using assms by blast
next
  show "A4meets P (A4join P Q)" using A4meets.simps A4join.simps A4Lines_def assms by (simp add: all_pairs)
next
  show "A4meets Q (A4join P Q)" using A4meets.simps A4join.simps A4Lines_def assms by (simp add: all_pairs)
qed

*)
theorem A2_a1a1: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2join P Q \<in> A2Lines"
proof -
  show ?thesis   by (simp add: A2Lines_def)
qed



theorem A2_a1a2: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2meets P (a2join P Q)"
proof -
  show ?thesis
  proof -
    fix x0 y0 assume Pcoords: "P = (A2Point x0 y0)"
    fix x1 y1 assume Qcoords: "Q = (A2Point x1 y1)" 
    have 0: "a2meets P (a2join P Q)" 
    proof (cases "(x0 = x1)")
      case True (* Case where x0 = x1 *)
      have 0: "a2join P Q =  A2Vertical x0" using True assms Pcoords Qcoords by auto
      have 1: "a2meets P (A2Vertical x0)" using True assms Pcoords a2meets.simps by blast
      thus "a2meets P (a2join P Q)" using 0 1 by auto
    next
      case False
      have 0: "a2join P Q =  (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))" using False assms Pcoords Qcoords a2join.simps by auto
      have 1: "a2meets P (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))" using False assms Pcoords a2meets.simps by simp
      thus "a2meets P (a2join P Q)" using 0 1 by auto
    qed 
  next
    show 1: "a2meets P (a2join P Q)" 
      by (smt (verit, ccfv_threshold) a2join.elims a2ln.simps(1) a2ln.simps(3) a2meets.elims(3) a2meets.simps(2) a2pt.inject assms(1) mult.commute times_divide_eq_left)
  qed
qed

theorem A2_a1a3: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2meets Q (a2join P Q)"
proof -
  obtain x0 y0 where Pcoords: "P = (A2Point x0 y0)" using a2pt.exhaust by auto
  obtain x1 y1 where Qcoords: "Q = (A2Point x1 y1)" using a2pt.exhaust by auto
  have 0: "a2meets Q (a2join P Q)" 
    proof (cases "(x0 = x1)")
      case True (* Case where x0 = x1 *)
      have 0: "a2join P Q =  A2Vertical x0" using True assms Pcoords Qcoords by auto
      have 1: "a2meets Q (A2Vertical x0)" using True assms Qcoords a2meets.simps by blast
      thus "a2meets Q (a2join P Q)" using 0 1 by auto
    next
      case False
      have 0: "a2join P Q =  (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))" using False assms Pcoords Qcoords a2join.simps by auto
      have 1: "a2meets Q (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))" 
      proof -
        have J1: "a2meets Q (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0))) = 
          a2meets (A2Point x1 y1) (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))" using Qcoords by auto
        have J2: "(a2meets (A2Point x1 y1) (A2Ordinary ((y1 - y0)/(x1-x0)) (y0 - x0* (y1 - y0)/(x1-x0)))) = 
          (y1 = (((y1 - y0)/(x1-x0))*x1 +  (y0 - x0* (y1 - y0)/(x1-x0))))" using a2meets.simps by blast
        have J3: "(y1 = (((y1 - y0)/(x1-x0))*x1 +  (y0 - x0* (y1 - y0)/(x1-x0)))) =
                (y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0 - x0* (y1 - y0)/(x1-x0))))"  by (simp add: left_diff_distrib')
        have J4: "(y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0 - x0* (y1 - y0)/(x1-x0)))) = 
              (y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0 - (x0*y1 - x0*y0)/(x1-x0))))"  by (simp add: right_diff_distrib)
        have J5: "(y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0 - (x0*y1 - x0*y0)/(x1-x0)))) =
              (y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0*(x1-x0)/(x1-x0) - (x0*y1 - x0*y0)/(x1-x0))))"  using False by auto
        have J6: "(y1 = (((y1*x1 - y0*x1)/(x1-x0)) +  (y0*(x1-x0)/(x1-x0) - (x0*y1 - x0*y0)/(x1-x0)))) =
              (y1 = (((y1*x1 - y0*x1 + y0*(x1-x0))/(x1-x0))  - (x0*y1 - x0*y0)/(x1-x0)))" by argo
        have J7: "(y1 = (((y1*x1 - y0*x1 + y0*(x1-x0))/(x1-x0))  - (x0*y1 - x0*y0)/(x1-x0))) = 
              (y1 = (((y1*x1 - y0*x1 + y0*(x1-x0) -(x0*y1 - x0*y0) )/(x1-x0))))" by argo
        have J8: "(y1 = (((y1*x1 - y0*x1 + y0*(x1-x0) -(x0*y1 - x0*y0) )/(x1-x0)))) = 
                  (y1 = (((y1*x1 - y0*x1 + y0*x1-y0*x0) - x0*y1 + x0*y0)/(x1-x0)))" by argo
        have J9: "(y1 = (((y1*x1 - y0*x1 + y0*x1-y0*x0) - x0*y1 + x0*y0)/(x1-x0))) =
                  (y1 = ((y1*x1 - y0*x1 + y0*x1 - x0*y1 )/(x1-x0)))" by argo
        have J10: "(y1 = ((y1*x1 - y0*x1 + y0*x1 - x0*y1 )/(x1-x0))) =
                   (y1 = ((y1*(x1-x0) )/(x1-x0)))" by argo
        have J11: "(y1 = ((y1*(x1-x0) )/(x1-x0)))" using False by auto
        show ?thesis using J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 J11 by auto
      qed
      thus 3:?thesis using 0 by simp
    qed
    show ?thesis using 0 by auto
  qed 

theorem A2_a1a: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows "a2join P Q \<in> A2Lines" and "a2meets P (a2join P Q)" and "a2meets Q (a2join P Q)"
proof -
  show "a2join P Q \<in> A2Lines" using assms A2_a1a1 by blast
  show "a2meets P (a2join P Q)" using assms A2_a1a2 by blast
  show "a2meets Q (a2join P Q)" using assms A2_a1a3 by blast
qed

text\<open>\done For this next theorem, it might make sense to phrase it as "P notequal Q lets us derive a unique
line l such that..."
but that would require proving the existence of l (which we just did in the previous lemma) and
then proving that it's unique. Instead, we can just say that if l and m both contain the 
distinct points P and Q, then l must equal m. From this, and the previous lemma, we can then 
conclude that axiom 1 is true (which we'll do in a final theorem). 

This is arguably the ugliest theorem in the bunch, because it involves four cases (one each for 
l and m being ordinary or vertical). Once again, we start by providing names for the constructor
arguments for P and Q:
 \seiji\<close>

lemma A2_a1b: 
  fixes P :: a2pt
  fixes Q
  fixes l
  assumes pq: "P \<noteq> Q"
  assumes pl : "a2meets P l"
  assumes ql : "a2meets Q l"
  shows "l = a2join P Q"

proof - 
  obtain x0 y0 where Pcoords: "P = (A2Point x0 y0)"  using a2pt.exhaust by auto
  obtain x1 y1 where Qcoords: "Q = (A2Point x1 y1)"  using a2pt.exhaust by auto
  show ?thesis
  proof (cases "(x0 = x1)")
    case True
    then show ?thesis using Pcoords Qcoords a2meets.elims(2) pl pq ql by fastforce
  next  
    case False
    obtain m b  where Lcoords: "l = (A2Ordinary m b)" using False a2join.simps
    by (metis Pcoords Qcoords a2ln.exhaust a2meets.simps(2) pl ql)

    have 1: "(a2meets P l) = (m*x0 + b = y0)" using False a2meets.simps Lcoords Pcoords by auto
    have 2: "(a2meets Q l) = (m*x1 + b = y1)" using False a2meets.simps Lcoords Qcoords by auto
    have 3: "m * (x1 - x0) = y1 - y0" using 1 2 pl ql by argo
    have 4: "m = (y1 - y0)/(x1 - x0)" using False 3 by (simp add: nonzero_eq_divide_eq)
    have 5: " (y1 - y0)/(x1 - x0)*x1 + b = y1" using 2 4 assms by auto
    have 6: "b = y1 - x1* (y1 - y0)/(x1 - x0)" using 5 by argo
    thus ?thesis using 1 4 6 Lcoords Pcoords Qcoords a2join.simps False 
    by (metis  add.commute  eq_diff_eq mult.commute pl times_divide_eq_right)
  qed
qed

(* (A2Ordinary ((y2 - y1)/(x2-x1)) (y1 - x1* (y2 - y1)/(x2-x1))))" *)


text \<open>\done Whew! We've proved axiom 1 for the real affine plane. On to Axiom 2. This one's 
a little trickier because we're proving a conjunction. \caleb\<close>


(*
    a2: "\<lbrakk>\<not> meets P l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> 
    find_parallel l P \<in> Lines \<and> ( find_parallel l P) || l \<and> meets P (find_parallel l P)" and
*)

lemma A2_a2a:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2meets P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" (* vacuous here, but parallel to the A4 case *)
  shows  "a2find_parallel l P \<in> A2Lines"
proof -
  show ?thesis using A2Lines_def by auto
qed


(*
fun a2find_parallel::"a2ln \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"a2find_parallel (A2Ordinary m b) (A2Point x y)  = (A2Ordinary m (y-m*x))" |
"a2find_parallel  (A2Vertical xi) (A2Point x y) = (A2Vertical x)"

*)
lemma A2_a2b:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2meets P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" (* vacuous here, but parallel to the A4 case *)
  shows   "(a2find_parallel l P) a2|| l"
proof -
  obtain x0 y0 where Pcoords: "P = (A2Point x0 y0)" using a2meets.elims by metis
  show ?thesis 
  proof (cases l)
    case (A2Vertical x1)
    have 0: "a2find_parallel l P = A2Vertical x0" using a2find_parallel.cases assms  A2Vertical Pcoords by simp 
    have 1: "A2Vertical x0 a2|| l"  by (metis A2Vertical a2meets.simps(2) a2parallel_def a2pt.exhaust)
    thus ?thesis using 0 1 by auto
  next
    case (A2Ordinary m b)
    have 0: "a2find_parallel l P = (A2Ordinary m (y0-m*x0))" using a2find_parallel.cases assms  A2Ordinary Pcoords by simp 
    thus ?thesis using 0 a2parallel_def assms Pcoords a2meets.elims by (smt (verit) A2Ordinary a2meets.simps(1))
  qed
qed

lemma A2_a2c:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2meets P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" (* vacuous here, but parallel to the A4 case *)
  shows  "a2meets P  (a2find_parallel l P)" 
proof -
  obtain x0 y0 where Pcoords: "P = (A2Point x0 y0)" using a2meets.elims by metis
  show ?thesis 
  proof (cases l)
    case (A2Vertical x1)
    have 0: "a2find_parallel l P = A2Vertical x0" using a2find_parallel.cases assms  A2Vertical Pcoords by simp 
    have 1: "a2meets P (A2Vertical x0)" using Pcoords a2meets.simps A2Vertical by auto
    thus ?thesis using 0 1 by auto
  next
    case (A2Ordinary m b)
    have 0: "a2find_parallel l P = (A2Ordinary m (y0-m*x0))" using a2find_parallel.cases assms  A2Ordinary Pcoords by simp 
    have 1: "a2meets P (A2Ordinary m (y0-m*x0))" using Pcoords a2meets.simps A2Ordinary by auto
    thus ?thesis using 0 1 by auto 
  qed
qed



lemma A2_a2:
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> (a2meets P l)"
  assumes "P \<in> A2Points" and "l \<in> A2Lines" (* vacuous here, but parallel to the A4 case *)
  shows  "a2find_parallel l P \<in> A2Lines" and   "(a2find_parallel l P) a2|| l" and "a2meets P  (a2find_parallel l P)" 
proof -
  show "a2find_parallel l P \<in> A2Lines" using A2_a2a A2Lines_def by auto 
  show "(a2find_parallel l P) a2|| l" using A2_a2b assms by auto
  show "a2meets P  (a2find_parallel l P)" using assms A2_a2c by auto
qed





text \<open> \spike At this point, I went down a rabbit hole searching for proofs of the other half

of axiom 2, and kept getting into trouble when dealing with the (pretty simple) algebra 
of straight lines. So I backed off and proved a bunch of small lemmas, partly as practice 
at proving things, and partly to give Isabelle a helping hand when it came to more complicated
things. So here are proofs of things like "a vertical and ordinary line cannot be parallel; if two 
ordinary lines have different slopes, then they intersect; if two vertical lines intersect, they're 
the same; if two ordinary lines with the same slope intersect, then they're the same; if two
ordinary lines are parallel and intersect, then they're the same. \done \<close>

text\<open> Let's start with something dead simple: the other form of parallelism: if 
there's no P meeting both l and m, then they're parallel. \caleb\<close>

lemma A2_parallel_0: 
  fixes l
  fixes m
  fixes P
  assumes nomeet: "\<not> (\<exists>P . a2meets P l \<and> a2meets P m)"
  shows "l a2|| m"

  using a2parallel_def nomeet by auto


text \<open>\done a vertical and ordinary line cannot be parallel \caleb \<close>
lemma A2_basics_1: 
  fixes l
  fixes m
  assumes lo: "l = A2Vertical x"
  assumes mo: "m = A2Ordinary s b "
  shows lm_noparr : "\<not> (l a2|| m)"
proof -

  obtain P where P: "P = (A2Point x (x * s + b)) \<and> a2meets P m"
    using mo by force
  have "a2meets P l"
    by (simp add: P lo)
  thus ?thesis
    using P a2parallel_def lo mo by blast

qed

text \<open>\done if two ordinary lines have different slopes, then they intersect \caleb \<close>
lemma A2_basics_2: 
  fixes l
  fixes m
  assumes lo: "l = A2Ordinary s1 b1"
  assumes mo: "m = A2Ordinary s2 b2"
  assumes sdiff: "s1 \<noteq> s2"
  shows lm_noparr2 : "\<not> (l a2|| m)"
proof - 
  obtain x where x: "x = (b2 - b1) / (s1 - s2)"
    by simp
  obtain y where y: "y = s1 * x + b1"
    by simp
  obtain P where P: "P = (A2Point x y)"
    by simp
  have pl: "a2meets P l"
    by (simp add: P lo y)
  have eq1: "s1 * x + b1 = s1 * (b2 - b1) / (s1 - s2) + b1" by (simp add: x)
  have eq2: "s1 * (b2 - b1) / (s1 - s2) + b1 = (b2 * s1 - b1 * s1) / (s1 - s2) + b1"
    by argo
  have eq3: "(b2 * s1 - b1 * s1) / (s1 - s2) + b1 = (b2 * s1 - b1 * s1) / (s1 - s2) + (s1 * b1 - s2 * b1) / (s1 - s2)" 
    by (simp add: mult_diff_mult sdiff)
  have eq4: "(b2 * s1 - b1 * s1) / (s1 - s2) + (s1 * b1 - s2 * b1) / (s1 - s2) =  (s1 * b2 - b1 * s2) / (s1 - s2)" 
    by argo
  have eq5: "s2 * x + b2 = s2 * (b2 - b1) / (s1 - s2) + b2" by (simp add: x)
  have eq6: "s2 * (b2 - b1) / (s1 - s2) + b2 = (b2 * s2 - b1 * s2) / (s1 - s2) + b2"
    by argo
  have eq7: "(b2 * s2 - b1 * s2) / (s1 - s2) + b2 = (b2 * s2 - b1 * s2) / (s1 - s2) + (s1 * b2 - s2 * b2) / (s1 - s2)" 
    by (simp add: mult_diff_mult sdiff)
  have eq8: "(b2 * s2 - b1 * s2) / (s1 - s2) + (s1 * b2 - s2 * b2) / (s1 - s2) =  (s1 * b2 - b1 * s2) / (s1 - s2)"
    by argo
  have eq9: "y = s2 * x + b2"
    by (simp add: eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 y)
  have pm: "a2meets P m" 
    by (simp add: P mo eq9)
  thus ?thesis
    using a2parallel_def lo mo pl sdiff by auto   
qed

text\<open>\done Trying to prove axiom 2 directly seems near impossible. Let's start with 
something simpler: if l and m are parallel, and l is vertical, so is m (and similarly
for ordinary) \caleb\<close>

(*
    a2: "\<lbrakk>\<not> meets P l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> find_parallel l P \<in> Lines \<and> ( find_parallel l P) || l \<and> meets P (find_parallel l P)" and
    a3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)"
*)
lemma A2_a3:
  shows  "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> (\<nexists> m. a2meets P m \<and> a2meets Q m \<and> a2meets R m)"
proof -
  obtain P where P: "P = (A2Point 0 0)" by simp
  obtain Q where Q: "Q = (A2Point 1 0)" by simp
  obtain R where R: "R = (A2Point 0 1)" by simp

  have "(\<nexists> m. a2meets P m \<and> a2meets Q m \<and> a2meets R m)"
    by (metis A2_a1b P Q R a2meets.simps(2) a2pt.inject zero_neq_one)

  thus ?thesis 
  by (metis (full_types) P a2pt.inject zero_neq_one)
qed

text\<open>\done \done\<close>


text\<open> At this point we've established that the Cartesian Plane satisfies Cartesian 
versions of the three axioms, etc., but it'd be nice to be able to say that as
a *structure*, it matches the Isabelle "locale" that we defined. \caleb \seiji 
\<close>

theorem A2_affine: "affine_plane A2Points A2Lines a2meets a2join a2find_parallel"
  unfolding affine_plane_def
proof (intro conjI)
  show 11: "\<forall>P Q. P \<noteq> Q \<longrightarrow>
            P \<in> A2Points \<longrightarrow>
            Q \<in> A2Points \<longrightarrow>
            a2join P Q
            \<in> A2Lines \<and>
            a2meets P
             (a2join P Q) \<and>
            a2meets Q
             (a2join P Q)"   using A2_a1a A2_a1b by auto    
next
  show 12: "\<forall>P Q m.
       P \<noteq> Q \<longrightarrow>
       P \<in> A2Points \<longrightarrow>
       Q \<in> A2Points \<longrightarrow>
       a2meets P m \<longrightarrow>
       a2meets Q m \<longrightarrow>
       m = a2join P Q" using A2_a1b by auto
next
  show 2: " \<forall>P l. \<not> a2meets P l \<longrightarrow>
          P \<in> A2Points \<longrightarrow>
          l \<in> A2Lines \<longrightarrow>
          a2find_parallel l P
          \<in> A2Lines \<and>
          affine_plane_data.parallel
           A2Points A2Lines
           a2meets
           (a2find_parallel l
             P)
           l \<and>
          a2meets P
           (a2find_parallel l
             P)" using A2_a2a A2_a2b A2_a2c a2parallel_def affine_plane_data.parallel_def by metis
next
  show 3: "\<exists>P Q R.
       P \<in> A2Points \<and>
       Q \<in> A2Points \<and>
       R \<in> A2Points \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> affine_plane_data.collinear
           A2Points A2Lines
           a2meets P Q R" using A2_a3  by (metis A2Points_def UNIV_I affine_plane_data.collinear.elims(2))
qed

(* Yay! We've proved the euclidean plane is an affine plane! *)
end


