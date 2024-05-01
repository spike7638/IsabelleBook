theory A4Bad2
  imports Complex_Main 
begin
(*
Slightly improve things by making the lines a type, and having points be a function 
that takes a line to the associated point-set (i.e., do our best to leave sets out of the discussion
The tailor strikes again!
*)
locale affine_plane_data =
  fixes Points :: "'p set" and Lines :: "'l set" and meets :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes join:: "'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel:: "'l \<Rightarrow> 'p \<Rightarrow> 'l"
begin

definition parallel::"'l \<Rightarrow> 'l \<Rightarrow> bool"  (infix "||" 5)  where
  "parallel l m = (if (l \<in> Lines \<and> m \<in> Lines) 
  then l = m \<or> \<not> (\<exists> P. P \<in> Points \<and> meets P l \<and> meets P m) else undefined)"

lemma parallel_self [iff]: 
  fixes l
  assumes "l \<in> Lines"
  shows "parallel l l"
  unfolding parallel_def using assms by simp

lemma parallel_if_no_shared_pointsI [intro]:
  assumes " \<not> (\<exists> P. P \<in> Points \<and> meets P l \<and> meets P m)" and
  "l \<in> Lines" and "m \<in> Lines"
  shows "l || m"
  using assms unfolding parallel_def
  by auto

lemma parallel_if_no_shared_points2I [intro]:
  assumes "\<forall>P .  P \<notin>  Points \<or> \<not> meets P l \<and>  \<not>meets P m" and
  "l \<in> Lines" and "m \<in> Lines"
  shows "l || m"
  using assms  parallel_if_no_shared_pointsI by auto

lemma parallelE [elim]:
  assumes "parallel l m"  and
  "l \<in> Lines" and "m \<in> Lines"
  obtains (eq) "l = m" | (disjoint) "\<not> (\<exists> P. P \<in> Points \<and> meets P l \<and> meets P m)"
  using assms unfolding parallel_def by auto

fun collinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
    where "collinear A B C = (if A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
  then (\<exists> l. l \<in> Lines \<and> meets A l \<and> meets B l \<and> meets C l) else undefined)"
end

locale affine_plane =
    affine_plane_data  +
    assumes
    a1a: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> join P Q \<in> Lines \<and> meets P (join P Q)  \<and> meets Q (join P Q)" and
    a1b: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points; meets P m; meets Q m\<rbrakk> \<Longrightarrow> m = join P Q" and
    a2a: "\<lbrakk>\<not> meets P l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> find_parallel l P \<in> Line" and
    a2b: "\<lbrakk>\<not> meets P l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow>  ( find_parallel l P) || l" and
    a2c: "\<lbrakk>\<not> meets P l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow>  meets P (find_parallel l P)" and
    a3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)"
begin
(* to do
define "liesOn", "contains", join(P, Q), crossing(n, k)
.Show join(P, Q) = join(Q, P); 
x crossing(n, k) = crossing(k, n). 
P liesOn m <-> m contains P, 
x n contains crossing(n, k) 
x k contains crossing(n, k)
.join(P, Q) contains P
.join(P, Q) contains Q
*)

(*
fun crossing:: "'l \<Rightarrow> 'l \<Rightarrow> 'p" where
  crossing n k = (if (n \<in> Lines \<and> k \<in> Lines \<and> \<not>(n || k)) 
  then l = m \<or> \<not> (\<exists> P. P \<in> Points \<and> meets P l \<and> meets P m) else undefined)"
*)


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

(*
lemma crossing_symmetric: 
  fixes n k
  assumes "n \<in> Lines"
  assumes "k \<in> Lines"
  assumes "n \<noteq> k" 
  shows "join P Q = join Q P" 
proof -
  have 2: "meets P (join Q P)" using assms a1a by auto
  have 3: "meets Q (join Q P)" using assms a1a by auto
  have "join Q P = join P Q" using assms 2 3  a1b by blast
  then show ?thesis by auto
qed
*)


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
end
(*
.define "liesOn", "contains", join(P, Q)
.Show join(P, Q) = join(Q, P); 
.P liesOn m <-> m contains P, 
.join(P, Q) contains P
.join(P, Q) contains Q
*)

(* Let's show that the 4-point affine plane is an affine plane. That entails creating Point, Lines, contains, and join. 
*)

datatype a4pt = Pa | Qa | Ra | Sa

definition "A4Points = {Pa, Qa, Ra, Sa}"
datatype a4line = A4PQ | A4PR | A4PS | A4QR | A4QS | A4RS
definition "A4Lines = {A4PQ, A4PR, A4PS,  A4QR, A4QS, A4RS}"

fun points :: "a4line \<Rightarrow> a4pt set" where
  "points A4PQ = {Pa, Qa}"
| "points A4PR = {Pa, Ra}"
| "points A4PS = {Pa, Sa}"
| "points A4QR = {Qa, Ra}"
| "points A4QS = {Qa, Sa}"
| "points A4RS = {Ra, Sa}"

definition "A4parallel (l::a4line)  (m::a4line) \<equiv> l = m \<or> (points l \<inter> points m = {})"

lemma parallel_self [iff]: "A4parallel l l"
  unfolding A4parallel_def by simp

lemma parallel_if_points_inter_eq_emptyI [intro]:
  assumes "points l \<inter> points m = {}"
  shows "A4parallel l m"
  using assms unfolding A4parallel_def by simp

lemma parallelE [elim]:
  assumes "A4parallel l m"
  obtains (eq) "l = m" | (disjoint) "points l \<inter> points m = {}"
  using assms unfolding A4parallel_def by auto

fun A4complement::"a4line \<Rightarrow> a4line" where
  "A4complement A4PQ = A4RS"
| "A4complement A4RS = A4PQ"
| "A4complement A4PR = A4QS"
| "A4complement A4QS = A4PR"
| "A4complement A4PS = A4QR"
| "A4complement A4QR = A4PS"

lemma A4complement_parallel:
  shows "A4parallel (A4complement n) n"
  by (cases n) auto

fun  A4join::"a4pt \<Rightarrow> a4pt \<Rightarrow> a4line"  where 
  "A4join Pa Pa = undefined"
| "A4join Pa Qa = A4PQ"
| "A4join Pa Ra = A4PR"
| "A4join Pa Sa = A4PS"
| "A4join Qa Pa = A4PQ"
| "A4join Qa Qa = undefined"
| "A4join Qa Ra = A4QR"
| "A4join Qa Sa = A4QS"
| "A4join Ra Pa = A4PR"
| "A4join Ra Qa = A4QR"
| "A4join Ra Ra = undefined"
| "A4join Ra Sa = A4RS"
| "A4join Sa Pa = A4PS"
| "A4join Sa Qa = A4QS"
| "A4join Sa Ra = A4RS"
| "A4join Sa Sa = undefined"

fun A4meets::"a4pt \<Rightarrow> a4line \<Rightarrow> bool" where
"A4meets x m = (x \<in> points m)"

fun A4find_parallel::"a4line \<Rightarrow> a4pt \<Rightarrow> a4line"  where
"A4find_parallel m T = (if T \<in> points m then m else (A4complement m))"


theorem PinPQ1:
  assumes   "P \<noteq> Q"
  shows "A4meets P (A4join P Q)" 
  
  using A4join.simps A4meets.elims points.simps
  by (metis (no_types, lifting) UnI2 a4pt.exhaust assms insertI1 insert_is_Un)

theorem QinPQ1:
  fixes P Q
  assumes   "P \<noteq> Q" 
  shows "A4meets Q  (A4join P Q)"
  using points.simps a4pt.simps A4join.simps
  by (metis PinPQ1 a4pt.exhaust assms)

theorem A4a1a1:
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points"
  shows "A4join P Q \<in> A4Lines"
  using A4Lines_def A4complement.elims by blast

(* "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> join P Q \<in> Lines \<and> meets P (join P Q)  \<and> meets Q (join P Q)" *)
theorem A4a1a2:
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points"
  shows "A4meets P (A4join P Q)"
  using PinPQ1 assms(1) by blast

theorem A4a1a3:
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points"
  shows "A4meets Q (A4join P Q)"
  using QinPQ1 assms(1) by blast 

theorem A4a1a: 
  assumes "P \<noteq> Q" and "P \<in> A4Points" and "Q \<in> A4Points"
  shows "A4join P Q \<in> A4Lines \<and> A4meets P (A4join P Q)  \<and> A4meets Q (A4join P Q)"
  using A4a1a1 A4a1a2 A4a1a3 assms by auto

theorem A4a1b: 
  assumes "P \<noteq> Q" and "P  \<in> A4Points" and "Q \<in> A4Points" and "m \<in> A4Lines"
  assumes "A4meets P m" and "A4meets Q m"
  shows "m = A4join P Q"
proof (cases P; cases Q)
  assume "P = Pa"
  assume "Q = Qa"
  show "m = A4join P Q"
    using assms A4Lines_def A4meets.elims a4pt.exhaust A4join.elims points.elims a4pt.distinct a4pt.simps
by (smt (verit) insertE insert_absorb singleton_insert_inj_eq')

 

(*
    a1b: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points; meets P m; meets Q m\<rbrakk> \<Longrightarrow> m = join P Q" and
    a2a: "\<lbrakk>\<not> meets P l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> find_parallel l P \<in> Line" and
    a2b: "\<lbrakk>\<not> meets P l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow>  ( find_parallel l P) || l" and
    a2c: "\<lbrakk>\<not> meets P l; P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow>  meets P (find_parallel l P)" and
    a3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)"
 
*)

lemma not_four_and:
  fixes p1 p2 p3 p4
  assumes "\<not> (p1 \<and> p2 \<and> p3 \<and> p4)"
  shows   "(\<not> p1) \<or> (\<not> p2) \<or> (\<not> p3) \<or> (\<not> p4)"
  using assms by blast

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
  show ?thesis 
  proof -

  have u0: "Pa \<in> A4Points" using A4Points_def by blast
  have u1: "Qa \<in> A4Points" using A4Points_def by blast
  have u2: "Ra \<in> A4Points" using A4Points_def by blast
  have d0:"Pa \<noteq> Qa" by simp
  have d1:"Pa \<noteq> Ra" by simp
  have d2:"Qa \<noteq> Ra" by simp
  have "\<not> (affine_plane_data.collinear
           A4Points A4Lines A4meets Pa Qa Ra)" 
  proof -
(*    have 0: "affine_plane_data.collinear A4Points A4Lines A4meets Pa Qa Ra = 
     (if Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points *)
    have 0: "affine_plane_data.collinear A4Points A4Lines A4meets Pa Qa Ra = 
 (\<exists> l. l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l \<and> A4meets Ra l)" 
      using affine_plane_data.collinear.simps u0 u1 u2 by auto
    fix l
    assume " l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l \<and> A4meets Ra l"
    have 
    have 3: "\<not>  (\<exists> l. l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l \<and> A4meets Ra l) =
          (\<forall> l . \<not> (l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l \<and> A4meets Ra l)) " by auto
    have 4: "(\<forall> l . \<not> (l \<in> A4Lines \<and> (A4meets Pa l) \<and> (A4meets Qa l) \<and> (A4meets Ra l)))  = 
          (\<forall> l .(\<not> ( l \<in> A4Lines)) \<or> (\<not> (A4meets Pa l)) \<or>  (\<not> (A4meets Qa l)) \<or> ( \<not> (A4meets Ra l)))" 
      using  not_four_and by auto
    have 5: "\<not>  (\<exists> l. l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l \<and> A4meets Ra l) = 
         (\<forall> l .(\<not> ( l \<in> A4Lines)) \<or> (\<not> (A4meets Pa l)) \<or>  (\<not> (A4meets Qa l)) \<or> ( \<not> (A4meets Ra l)))" 
      using 3 4 by auto
    fix l
    have 6: "(\<not> ( l \<in> A4Lines)) \<or> (\<not> (A4meets Pa l)) \<or>  (\<not> (A4meets Qa l)) \<or> ( \<not> (A4meets Ra l)) = 
      (\<not> (( l \<in> A4Lines) \<and> (A4meets Pa l) \<and> (A4meets Qa l) \<and> (A4meets Ra l)))" by auto
    have 7: "(A4meets Pa l) = (l = A4PQ) \<or> (l = A4PR) \<or> (l = A4PS)" using A4meets.simps points.simps
    proof -
      have f1: "{Ra, Sa} \<noteq> {Ra} \<union> {Sa} \<or> points A4RS \<noteq> {Ra, Sa} \<or> {Ra} \<union> {Sa} = points l \<or> l \<noteq> A4RS"
        by force
      have "{Qa, Ra} \<noteq> {Qa} \<union> {Ra} \<or> points A4QR \<noteq> {Qa, Ra} \<or> {Qa} \<union> {Ra} = points l \<or> l \<noteq> A4QR"
        by blast
      then show ?thesis
        using f1 by (smt (z3) A4complement.elims A4join.simps(5) A4meets.simps QinPQ1 Un_iff a4pt.simps(2) a4pt.simps(4) a4pt.simps(6) insert_absorb insert_is_Un points.simps(4) points.simps(5) points.simps(6) singleton_insert_inj_eq)
    qed
    have 8: "(A4meets Qa l) = (l = A4PQ)" using 7  by auto
    have 11: "((A4meets Pa l) \<and> (A4meets Qa l) \<and> (A4meets Ra l)) = False" using 9 10 by auto
    then show ?thesis
      by (metis "0" A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4meets.elims(2) d0 d1 d2 empty_iff insert_iff u0 u1 u2)
  qed
  show ?thesis
    using \<open>\<not> affine_plane_data.collinear A4Points A4Lines A4meets Pa Qa Ra\<close> u0 u1 u2 by blast
qed
qed


theorem A4affine_plane_a1a: " \<And>P Q. P \<noteq> Q \<Longrightarrow>
           P \<in> A4Points \<Longrightarrow> Q \<in> A4Points \<Longrightarrow> A4join P Q \<in> A4Lines \<and> A4meets P (A4join P Q) \<and> A4meets Q (A4join P Q)"
proof -
  show " \<And>P Q. P \<noteq> Q \<Longrightarrow>
           P \<in> A4Points \<Longrightarrow> Q \<in> A4Points \<Longrightarrow> A4join P Q \<in> A4Lines \<and> A4meets P (A4join P Q) \<and> A4meets Q (A4join P Q)"  
  proof -
    fix P::a4pt
    fix Q::a4pt
    assume a0: "P \<noteq> Q"
    show "P \<in> A4Points \<Longrightarrow> Q \<in> A4Points \<Longrightarrow> A4join P Q \<in> A4Lines \<and> A4meets P (A4join P Q) \<and> A4meets Q (A4join P Q)" 
    proof (intro conjI)
      show "P \<in> A4Points \<Longrightarrow>
    Q \<in> A4Points \<Longrightarrow>
    A4join P Q \<in> A4Lines" using a0 all_joins_are_lines by auto
    next
      show "P \<in> A4Points \<Longrightarrow> Q \<in> A4Points \<Longrightarrow> A4meets P (A4join P Q)"
        using a0 all_joins_are_lines by auto
    next
      show "P \<in> A4Points \<Longrightarrow> Q \<in> A4Points \<Longrightarrow> A4meets Q (A4join P Q)"
        using a0 all_joins_are_lines by auto
    qed
  qed
qed

theorem A4affine_plane_a1b:  
  fixes P Q
  assumes 
    "P \<noteq> Q" and 
    "P \<in> A4Points" and  "Q \<in> A4Points" and
    "A4meets P m" and "A4meets Q m"
  shows "m = A4join P Q"
proof (cases "P")
  case Pa
    have Pfact: "P = Pa"
      by (simp add: Pa) 
  then show ?thesis 
  proof (cases "Q")
    case Pa
    have Qfact: "Q = Pa"
      by (simp add: Pa) 
    have False using assms Pfact Qfact by auto
    then show ?thesis by auto
  next
    case Qa
    have Qfact: "Q = Qa"
      by (simp add: Qa)
    have j1: "A4join P Q = {Pa, Qa}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4PQ" using A4PQ_def j1  by auto
    have mP: "A4meets Pa m" using assms Pfact by auto
    have mQ: "A4meets Qa m" using assms Qfact by auto
    have ss1: "m = A4PQ \<or> m = A4PR \<or> m = A4PS" using mP A4meets.simps
      by (metis A4Lines_def A4QR_def A4QS_def A4RS_def a4pt.simps(1) a4pt.simps(3) a4pt.simps(5) empty_iff insert_iff)
    have ss2: "m = A4PQ \<or> m = A4QR \<or> m = A4QS" using mQ A4meets.simps
      by (metis A4PR_def A4PS_def a4pt.simps(1) a4pt.simps(7) a4pt.simps(9) empty_iff insert_iff ss1)
    have mPQ: "m = A4PQ" using ss1 ss2 A4QR_def A4QS_def A4meets.elims(2) Pfact Qfact assms(4) by auto 

    then show ?thesis using j2 by auto
  next
    case Ra
    have Qfact: "Q = Ra"
    by (simp add: Ra)
    have j1: "A4join P Q = {Pa, Ra}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4PR" using A4PR_def j1  by auto
    have mP: "A4meets Pa m" using assms Pfact by auto
    have mQ: "A4meets Ra m" using assms Qfact by auto
    have ss1: "m = A4PQ \<or> m = A4PR \<or> m = A4PS" using mP A4meets.simps
      by (metis A4Lines_def A4QR_def A4QS_def A4RS_def a4pt.simps(1) a4pt.simps(3) a4pt.simps(5) empty_iff insert_iff)
    have ss2: "m = A4PR \<or> m = A4QR \<or> m = A4RS" using mQ A4meets.simps
      by (metis A4PQ_def A4PS_def a4pt.simps(11) a4pt.simps(3) a4pt.simps(7) insertE singletonD ss1) 
    have mPQ: "m = A4PR" using ss1 ss2  A4meets.elims Pfact Qfact assms
      using A4QR_def A4RS_def by auto
    then show ?thesis using j2 by auto
  next
    case Sa
    have Qfact: "Q = Sa"
    by (simp add: Sa)
    have j1: "A4join P Q = {Pa, Sa}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4PS" using A4PS_def j1  by auto
    have mP: "A4meets Pa m" using assms Pfact by auto
    have mQ: "A4meets Sa m" using assms Qfact by auto
    have ss1: "m = A4PQ \<or> m = A4PR \<or> m = A4PS" using mP A4meets.simps
      by (metis A4Lines_def A4QR_def A4QS_def A4RS_def a4pt.simps(1) a4pt.simps(3) a4pt.simps(5) empty_iff insert_iff)
    have ss2: "m = A4PS \<or> m = A4QS \<or> m = A4RS" using mQ A4meets.simps
      by (metis A4PQ_def A4PR_def a4pt.simps(11) a4pt.simps(5) a4pt.simps(9) insertE singletonD ss1) 
    have mPQ: "m = A4PS" using ss1 ss2  A4meets.elims Pfact Qfact assms
      using A4QS_def A4RS_def by auto
    then show ?thesis using j2 by auto
  qed
next
  case Qa
  have Pfact: "P = Qa"
      by (simp add: Qa) 
    then show ?thesis 
    proof (cases "Q")
    case Qa
    have Qfact: "Q = Qa"
      by (simp add: Qa) 
    have False using assms Pfact Qfact by auto
    then show ?thesis by auto
  next
    case Pa
    have Qfact: "Q = Pa"
      by (simp add: Pa)
    have j1: "A4join P Q = {Pa, Qa}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4PQ" using A4PQ_def j1  by auto
    have mP: "A4meets Qa m" using assms Pfact by auto
    have mQ: "A4meets Pa m" using assms Qfact by auto
    have ss1: "m = A4PQ \<or> m = A4QR \<or> m = A4QS" using mP A4meets.simps
      by (metis A4Lines_def A4PR_def A4PS_def A4RS_def Qa Qfact a4pt.simps(7) a4pt.simps(9) assms(1) empty_iff insert_iff)

      have ss2: "m = A4PQ \<or> m = A4PR \<or> m = A4PS" using mQ A4meets.simps
        by (metis A4QR_def A4QS_def a4pt.simps(1) a4pt.simps(3) a4pt.simps(5) empty_iff insert_iff ss1)

    have mPQ: "m = A4PQ"
      by (metis A4PR_def A4PS_def A4QR_def A4QS_def a4pt.simps(1) a4pt.simps(3) a4pt.simps(5) doubleton_eq_iff ss1 ss2) 

    then show ?thesis using j2 by auto
  next
    case Ra
    have Qfact: "Q = Ra"
    by (simp add: Ra)
    have j1: "A4join P Q = {Qa, Ra}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4QR" using A4QR_def j1  by auto
    have mP: "A4meets Qa m" using assms Pfact by auto
    have mQ: "A4meets Ra m" using assms Qfact by auto
    have ss1: "m = A4PQ \<or> m = A4QR \<or> m = A4QS" using mP A4meets.simps
      by (metis A4Lines_def A4PR_def A4PS_def A4RS_def a4pt.simps(1) a4pt.simps(7) a4pt.simps(9) empty_iff insert_iff)
     
    have ss2: "m = A4PR \<or> m = A4QR \<or> m = A4RS" using mQ A4meets.simps
      by (metis A4PQ_def A4QS_def Qa Ra a4pt.simps(11) a4pt.simps(3) assms(1) empty_iff insertE ss1)

    have mPQ: "m = A4QR" using ss1 ss2  A4meets.elims Pfact Qfact assms
      using A4PQ_def A4QS_def by auto
    then show ?thesis using j2 by auto
  next
    case Sa
    have Qfact: "Q = Sa"
    by (simp add: Sa)
    have j1: "A4join P Q = {Qa, Sa}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4QS" using A4QS_def j1  by auto
    have mP: "A4meets Qa m" using assms Pfact by auto
    have mQ: "A4meets Sa m" using assms Qfact by auto
    have ss1: "m = A4PQ \<or> m = A4QR \<or> m = A4QS" using mP A4meets.simps
       by (metis A4Lines_def A4PR_def A4PS_def A4RS_def a4pt.simps(1) a4pt.simps(7) a4pt.simps(9) empty_iff insert_iff)

      have ss2: "m = A4PS \<or> m = A4QS \<or> m = A4RS" using mQ A4meets.simps
        using A4PQ_def A4QR_def ss1 subset_singleton_iff by auto
        have mPQ: "m = A4QS" using ss1 ss2  A4meets.elims Pfact Qfact assms
      using A4PQ_def A4QR_def by auto
    then show ?thesis using j2 by auto
  qed
next
  case Ra
  have Pfact: "P = Ra"
      by (simp add: Ra) 
    then show ?thesis 
    proof (cases "Q")
    case Ra
    have Qfact: "Q = Ra"
      by (simp add: Ra) 
    have False using assms Pfact Qfact by auto
    then show ?thesis by auto
  next
    case Pa
    have Qfact: "Q = Pa"
      by (simp add: Pa)
    have j1: "A4join P Q = {Pa, Ra}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4PR" using A4PR_def j1  by auto
    have mP: "A4meets Ra m" using assms Pfact by auto
    have mQ: "A4meets Pa m" using assms Qfact by auto
    have ss1: "m = A4PR \<or> m = A4QR \<or> m = A4RS" using mP A4meets.simps
      by (metis A4Lines_def A4PQ_def A4PS_def A4QS_def a4pt.simps(11) a4pt.simps(3) a4pt.simps(7) insertE singletonD)

      have ss2: "m = A4PQ \<or> m = A4PR \<or> m = A4PS" using mQ A4meets.simps
        by (metis A4QR_def A4RS_def a4pt.simps(1) a4pt.simps(3) a4pt.simps(5) empty_iff insert_iff ss1)

    have mPQ: "m = A4PR"  using ss1 ss2  A4meets.elims Pfact Qfact assms
      using A4QR_def A4RS_def by auto

    then show ?thesis using j2 by auto
  next
    case Qa
    have Qfact: "Q = Qa"
    by (simp add: Qa)
    have j1: "A4join P Q = {Qa, Ra}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4QR" using A4QR_def j1  by auto
    have mP: "A4meets Ra m" using assms Pfact by auto
    have mQ: "A4meets Qa m" using assms Qfact by auto
    have ss1: "m = A4PR \<or> m = A4QR \<or> m = A4RS" using mP A4meets.simps
      by (metis A4Lines_def A4PQ_def A4PS_def A4QS_def Qfact Ra a4pt.simps(11) a4pt.simps(3) assms(1) insertE singletonD)
     
    have ss2: "m = A4PQ \<or> m = A4QR \<or> m = A4QS" using mQ A4meets.simps
      using A4PR_def A4RS_def a4pt.simps(9) ss1 by auto
    have mPQ: "m = A4QR" using ss1 ss2  A4meets.elims Pfact Qfact assms
      using A4PR_def A4RS_def by auto
    then show ?thesis using j2 by auto
  next
    case Sa
    have Qfact: "Q = Sa"
    by (simp add: Sa)
    have j1: "A4join P Q = {Ra, Sa}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4RS" using A4RS_def j1  by auto
    have mP: "A4meets Ra m" using assms Pfact by auto
    have mQ: "A4meets Sa m" using assms Qfact by auto
    have ss1: "m = A4PR \<or> m = A4QR \<or> m = A4RS" using mP A4meets.simps
      by (metis A4Lines_def A4PQ_def A4PS_def A4QS_def Ra Sa a4pt.simps(3) a4pt.simps(7) assms(1) insertE singletonD)

    have ss2: "m = A4PS \<or> m = A4QS \<or> m = A4RS" using mQ A4meets.simps
      using A4PR_def A4QR_def  ss1 by auto

    have mPQ: "m = A4RS" using ss1 ss2  A4meets.elims Pfact Qfact assms
      using A4PR_def A4QR_def by auto
    then show ?thesis using j2 by auto
  qed
next
  case Sa
  have Pfact: "P = Sa"
      by (simp add: Sa) 
    then show ?thesis
    proof (cases "Q")
    case Sa
    have Qfact: "Q = Sa"
      by (simp add: Sa) 
    have False using assms Pfact Qfact by auto
    then show ?thesis by auto
  next
    case Pa
    have Qfact: "Q = Pa"
      by (simp add: Pa)
    have j1: "A4join P Q = {Pa, Sa}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4PS" using A4PS_def j1  by auto
    have mP: "A4meets Sa m" using assms Pfact by auto
    have mQ: "A4meets Pa m" using assms Qfact by auto
    have ss1: "m = A4PS \<or> m = A4QS \<or> m = A4RS" using mP A4meets.simps
      by (metis A4Lines_def A4PQ_def A4PR_def A4QR_def a4pt.simps(11) a4pt.simps(5) a4pt.simps(9) empty_iff insert_iff)

      have ss2: "m = A4PQ \<or> m = A4PR \<or> m = A4PS" using mQ A4meets.simps
        by (metis A4QS_def A4RS_def Qfact Sa a4pt.simps(1) a4pt.simps(3) assms(1) empty_iff insert_iff ss1)

    have mPQ: "m = A4PS"  using ss1 ss2  A4meets.elims Pfact Qfact assms
      using A4QS_def A4RS_def by auto

    then show ?thesis using j2 by auto

  next
    case Qa
    have Qfact: "Q = Qa"
    by (simp add: Qa)
    have j1: "A4join P Q = {Qa, Sa}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4QS" using A4QS_def j1  by auto
    have mP: "A4meets Sa m" using assms Pfact by auto
    have mQ: "A4meets Qa m" using assms Qfact by auto
    have ss1: "m = A4PS \<or> m = A4QS \<or> m = A4RS" using mP A4meets.simps a4pt.simps
      by (metis A4Lines_def A4PQ_def A4PR_def A4QR_def insertE singletonD)
    have ss2: "m = A4PQ \<or> m = A4QR \<or> m = A4QS" using mQ A4meets.simps
      using A4PS_def A4RS_def ss1 by auto 
      have mPQ: "m = A4QS" using ss1 ss2  A4meets.elims Pfact Qfact assms
      using A4PS_def A4RS_def by auto
    then show ?thesis using j2 by auto
  next
    case Ra
    have Qfact: "Q = Ra"
    by (simp add: Ra)
    have j1: "A4join P Q = {Ra, Sa}" using Pfact Qfact A4join.simps by auto
    have j2: "A4join P Q = A4RS" using A4RS_def j1  by auto
    have mP: "A4meets Sa m" using assms Pfact by auto
    have mQ: "A4meets Ra m" using assms Qfact by auto
    have ss1: "m = A4PR \<or> m = A4QR \<or> m = A4RS" using mP A4meets.simps a4pt.simps
      by (metis A4Lines_def A4PQ_def A4PS_def A4QS_def insertE mQ singletonD)


    have ss2: "m = A4PS \<or> m = A4QS \<or> m = A4RS" using mQ A4meets.simps
      using A4PR_def A4QR_def Sa assms(1) assms(4) ss1 by auto
    have mPQ: "m = A4RS" using ss1 ss2  A4meets.elims Pfact Qfact assms
      using A4PR_def A4QR_def by auto
    then show ?thesis using j2 by auto
  qed
qed

(*
proof -
  show "\<And>P Q m.
       P \<noteq> Q \<Longrightarrow> P \<in> A4Points \<Longrightarrow> Q \<in> A4Points \<Longrightarrow> 
        A4meets P m \<Longrightarrow> A4meets Q m \<Longrightarrow> m = A4join P Q"
  proof -
    fix P::a4pt
    fix Q::a4pt
    proof (cases "Pair (P, Q)")
      case (Pair (Pa, Qa))
      show " \<And>Pa Qa m a b.
       Pa \<noteq> Qa \<Longrightarrow>
       Pa \<in> A4Points \<Longrightarrow>
       Qa \<in> A4Points \<Longrightarrow>
       A4meets Pa m \<Longrightarrow>
       A4meets Qa m \<Longrightarrow> (P, Q) = (a, b) \<Longrightarrow> m = A4join Pa Qa"
      proof -
   
  
  sorry
*)
lemma A4line_complement: 
  fixes l
  assumes "l \<in> A4Lines"
  shows "A4complement l \<in> A4Lines"
  by (smt (verit, best) A4Lines_def A4complement.simps assms empty_iff insert_iff)

lemma A4complement_parallel: 
  fixes n
  assumes "n \<in> A4Lines"
  shows "affine_plane_data.parallel A4Points A4Lines A4meets (A4complement n) n"

proof (cases "n = A4PQ")
  case True
  have 0: "n = A4PQ" using True
    by auto
  have 1: "A4complement n = A4RS" using A4complement.simps
    using \<open>n = A4PQ\<close> by auto
  have 2: "affine_plane_data.parallel A4Points A4Lines A4meets (A4RS) A4PQ = (if (A4RS \<in> A4Lines \<and> A4PQ \<in> A4Lines) 
  then A4RS = A4PQ \<or> \<not> (\<exists> P. P \<in>  A4Points \<and> A4meets P A4RS \<and> A4meets P A4PQ) else undefined)" using affine_plane_data.parallel.simps 0 1
  by (simp add: affine_plane_data.parallel.simps)
  show ?thesis using 2
    by (metis "0" "1" A4PQ_def A4RS_def A4line_complement A4meets.elims(2) a4pt.simps(3) a4pt.simps(5) a4pt.simps(7) a4pt.simps(9) assms insert_absorb insert_iff insert_not_empty) 
next
  show ?thesis
  proof (cases "n = A4PR")


theorem A4affine_plane_a2_alt:
  fixes P l
  assumes 
    "P \<notin> l" and
    "P \<in> A4Points" and
    "l \<in> A4Lines" 
  shows "A4complement l \<in> A4Lines \<and> affine_plane_data.parallel A4Points A4Lines A4meets (A4complement l) l \<and> (A4complement l) \<in> A4Lines"
proof -
  have 0: "A4complement l \<in> A4Lines" using A4line_complement assms(3) by auto
  


theorem A4affine_plane_a2: "\<And>P l. \<not> A4meets P l \<Longrightarrow>
           P \<in> A4Points \<Longrightarrow>
           l \<in> A4Lines \<Longrightarrow>
           A4find_parallel l P
           \<in> A4Lines \<and>
           affine_plane_data.parallel
            A4Points A4Lines
            A4meets
            (A4find_parallel l
              P)
            l \<and>
           A4meets P
            (A4find_parallel l
              P)"
proof (clarsimp)
  show "\<And>P l. P \<notin> l \<Longrightarrow>
           P \<in> A4Points \<Longrightarrow>
           l \<in> A4Lines \<Longrightarrow> A4Points - l \<in> A4Lines \<and> affine_plane_data.parallel A4Points A4Lines A4meets (A4Points - l) l \<and> A4Points - l \<in> A4Lines" 
  proof -
    fix P
    fix l
   show "P \<notin> l \<Longrightarrow>
           P \<in> A4Points \<Longrightarrow>
           l \<in> A4Lines \<Longrightarrow> A4Points - l \<in> A4Lines \<and> affine_plane_data.parallel A4Points A4Lines A4meets (A4Points - l) l \<and> A4Points - l \<in> A4Lines" using A4affine_plane_a2_alt 
     using  A4affine_plane_a2_alt by auto
 qed
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
