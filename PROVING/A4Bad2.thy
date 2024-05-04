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
    a2a: "\<lbrakk> P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> find_parallel l P \<in> Lines" and
    a2b: "\<lbrakk> P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow>  ( find_parallel l P) || l" and
    a2c: "\<lbrakk> P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow>  meets P (find_parallel l P)" and
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

fun  A4pencil::"a4pt \<Rightarrow> a4line set"  where 
   "A4pencil Pa = {A4PQ, A4PR, A4PS}"
|  "A4pencil Qa = {A4PQ, A4QR, A4QS}"
|  "A4pencil Ra = {A4PR, A4QR, A4RS}"
|  "A4pencil Sa = {A4PS, A4QS, A4RS}"


fun A4meets::"a4pt \<Rightarrow> a4line \<Rightarrow> bool" where
"A4meets x m = (x \<in> points m)"

fun A4find_parallel::"a4line \<Rightarrow> a4pt \<Rightarrow> a4line"  where
"A4find_parallel m T = (if T \<in> points m then m else (A4complement m))"

theorem line_in_pencil:
  assumes "A4meets P m"
  shows "m \<in> A4pencil P"
proof (cases P)
  case Pa
  have 0: "Pa \<in> points m"  using A4meets.simps assms Pa by auto
  have "m = A4PQ \<or> m = A4PR \<or> m = A4PS" using 0 points.simps
    by (metis a4pt.distinct(1) a4pt.distinct(3) a4pt.distinct(5) emptyE insertE points.cases) 
  then show ?thesis
    using A4pencil.simps(1) Pa by blast 
next
  case Qa
  have 0: "Qa \<in> points m"  using A4meets.simps assms Qa by auto
  have "m = A4PQ \<or> m = A4QR \<or> m = A4QS" using 0 points.simps
    by (metis a4pt.distinct(2) a4pt.distinct(8) a4pt.distinct(10)
 emptyE insertE points.cases)
  then show ?thesis
    using A4pencil.simps(2) Qa by blast
next
  case Ra
  have 0: "Ra \<in> points m"  using A4meets.simps assms Ra by auto
  have "m = A4PR \<or> m = A4QR \<or> m = A4RS" using 0 points.simps
    by (metis a4pt.distinct(4) a4pt.distinct(8) a4pt.distinct(12) emptyE insertE points.cases) 
  then show ?thesis
    using A4pencil.simps(3) Ra by blast
next
  case Sa
  have 0: "Sa \<in> points m"  using A4meets.simps assms Sa by auto
  have "m = A4PS \<or> m = A4RS \<or> m = A4QS" using 0 points.simps
    by (metis a4pt.distinct(6)  a4pt.distinct(10)  a4pt.distinct(12) emptyE insertE points.cases) 
  then show ?thesis
    using A4pencil.simps(4) Sa by blast
qed

theorem PinPQ1:
  assumes   "P \<noteq> Q"
  shows "A4meets P (A4join P Q)" 
  
  using A4join.simps A4meets.elims points.simps
  by (metis (no_types, lifting) UnI2 a4pt.exhaust assms insertI1 insert_is_Un)

theorem QinPQ1:
  fixes P Q
  assumes   "P \<noteq> Q" 
  shows "A4meets Q  (A4join P Q)"
  using points.simps a4pt.simps(1-12) A4join.simps 
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
  assumes "A \<noteq> B" and "A  \<in> A4Points" and "B \<in> A4Points" 
  assumes "A4meets A m" and "A4meets B m"
  shows "m = A4join A B"
proof -
  have 0:"m \<in> A4pencil A" using line_in_pencil assms by auto
  have 1:"m \<in> A4pencil B" using line_in_pencil assms by auto
  have 2:"m \<in> A4pencil A \<inter> A4pencil B" using 0 1 by auto
  show ?thesis 
  proof (cases A; cases B)
    assume A_point: "A = Pa" and B_point: "B = Pa"
    have z: False using assms A_point B_point by auto
    show ?thesis using z by auto
  next
    assume A_point: "A = Pa" and B_point: "B = Qa"
    have 0: "m = A4PQ" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)
  next
    assume A_point: "A = Pa" and B_point: "B = Ra"
    have 0: "m = A4PR" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)
  next
    assume A_point: "A = Pa" and B_point: "B = Sa"
    have 0: "m = A4PS" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)

  next
    assume A_point: "A = Qa" and B_point: "B = Qa"
    have z: False using assms A_point B_point by auto
    show ?thesis using z by auto
  next
    assume A_point: "A = Qa" and B_point: "B = Pa"
    have 0: "m = A4PQ" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)
  next
    assume A_point: "A = Qa" and B_point: "B = Ra"
    have 0: "m = A4QR" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)
  next
    assume A_point: "A = Qa" and B_point: "B = Sa"
    have 0: "m = A4QS" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)

  next
    assume A_point: "A = Ra" and B_point: "B = Ra"
    have z: False using assms A_point B_point by auto
    show ?thesis using z by auto
  next
    assume A_point: "A = Ra" and B_point: "B = Pa"
    have 0: "m = A4PR" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)
  next
    assume A_point: "A = Ra" and B_point: "B = Qa"
    have 0: "m = A4QR" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)
  next
    assume A_point: "A = Ra" and B_point: "B = Sa"
    have 0: "m = A4RS" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)

  next
    assume A_point: "A = Sa" and B_point: "B = Sa"
    have z: False using assms A_point B_point by auto
    show ?thesis using z by auto
  next
    assume A_point: "A = Sa" and B_point: "B = Pa"
    have 0: "m = A4PS" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)
  next
    assume A_point: "A = Sa" and B_point: "B = Qa"
    have 0: "m = A4QS" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)
  next
    assume A_point: "A = Sa" and B_point: "B = Ra"
    have 0: "m = A4RS" using 2 A_point B_point by auto
    thus ?thesis 
      by (simp add: A_point B_point)
  qed
qed

theorem A4a2a:
  assumes "P \<in> A4Points" and "l \<in> A4Lines"
  shows "A4find_parallel l P \<in> A4Lines"
proof -
  show ?thesis using A4Lines_def A4complement.cases by blast
qed

theorem A4a2b:
  assumes "P \<in> A4Points" and "l \<in> A4Lines"
  shows "affine_plane_data.parallel A4Points A4Lines A4meets (A4find_parallel l P) l" 
proof -
  show ?thesis unfolding affine_plane_data.parallel_def 
  proof -
    have h0:"A4find_parallel l P \<in> A4Lines \<and> l \<in> A4Lines" using assms A4a2a by auto
    have h1: "A4find_parallel l P = l \<or> (\<nexists>Pa. Pa \<in> A4Points \<and> A4meets Pa (A4find_parallel l P) \<and> A4meets Pa l)" 
      using assms A4a2a
      by (smt (z3) A4complement.simps(1) A4complement.simps(2) A4complement.simps(3) 
          A4complement.simps(4) A4complement.simps(5) A4complement.simps(6) 
          A4find_parallel.elims A4pencil.elims a4line.simps(12) 
          a4line.simps(14) a4line.simps(18) a4line.simps(2) a4line.simps(4) a4line.simps(6) 
          insertE line_in_pencil singletonD) 
    show "if A4find_parallel l P \<in> A4Lines \<and> l \<in> A4Lines
    then A4find_parallel l P = l \<or> (\<nexists>Pa. Pa \<in> A4Points \<and> A4meets Pa (A4find_parallel l P) \<and> A4meets Pa l) else undefined"
      using h0 h1 by auto
  qed
qed

theorem A4a2c:
  assumes "P \<in> A4Points" and "l \<in> A4Lines"
  shows "A4meets P (A4find_parallel l P)"
proof -
  show ?thesis using A4find_parallel.simps A4meets.simps assms
    by (smt (z3) A4complement.elims A4join.simps(10) A4join.simps(12) A4join.simps(2) A4join.simps(3)
        A4join.simps(4) A4join.simps(5) A4join.simps(7) A4join.simps(8) 
        A4pencil.cases QinPQ1 a4pt.distinct(1) a4pt.distinct(7) insertI1 
        points.simps(2) points.simps(3) points.simps(5) points.simps(6)) 
qed
(*  a1a: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> join P Q \<in> Lines \<and> meets P (join P Q)  \<and> meets Q (join P Q)" and
    a1b: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points; meets P m; meets Q m\<rbrakk> \<Longrightarrow> m = join P Q" and
    a2a: "\<lbrakk> P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow> find_parallel l P \<in> Lines" and
    a2b: "\<lbrakk> P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow>  ( find_parallel l P) || l" and
    a2c: "\<lbrakk> P \<in> Points; l \<in> Lines\<rbrakk> \<Longrightarrow>  meets P (find_parallel l P)" and
    a3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)"
*)

lemma not_four_and:
  fixes p1 p2 p3 p4
  assumes "\<not> (p1 \<and> p2 \<and> p3 \<and> p4)"
  shows   "(\<not> p1) \<or> (\<not> p2) \<or> (\<not> p3) \<or> (\<not> p4)"
  using assms by blast

theorem A4a3: " \<exists>P Q R.
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
  have u0: "Pa \<in> A4Points" using A4Points_def by blast
  have u1: "Qa \<in> A4Points" using A4Points_def by blast
  have u2: "Ra \<in> A4Points" using A4Points_def by blast
  have d0:"Pa \<noteq> Qa" by simp
  have d1:"Pa \<noteq> Ra" by simp
  have d2:"Qa \<noteq> Ra" by simp
  have basics: "Pa \<in> A4Points \<and>  Qa \<in> A4Points \<and> Ra \<in> A4Points \<and> 
      Pa \<noteq> Qa \<and> Pa \<noteq> Ra \<and> Qa \<noteq> Ra" using u0 u1 u2 d0 d1 d2 by blast
  show ?thesis 
  proof -
    presume r: "\<not> (affine_plane_data.collinear
           A4Points A4Lines A4meets Pa Qa Ra)" 
    show ?thesis using basics r by blast
  next
    have "affine_plane_data.collinear A4Points A4Lines A4meets Pa Qa Ra  =
     (if Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points 
  then (\<exists> l. l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l \<and> A4meets Ra l) else undefined)" 
      using affine_plane_data.collinear.simps
      by fastforce  
    also
    have 1: "... = (\<exists> l. (l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l) \<and> A4meets Ra l)" using u0 u1 u2 by auto
    also
    have 2: "... = (\<exists> l. l = A4PQ \<and> A4meets Ra l)" 
      by (metis A4a1a A4a1b A4join.simps(2) basics) 
    have 3: "... = False" using A4meets.simps by auto
    show "\<not> affine_plane_data.collinear A4Points A4Lines A4meets Pa Qa Ra" 
      using 2 3  calculation by blast 
  qed
qed

theorem A4_is_affine_plane: "affine_plane A4Points A4Lines A4meets A4join A4find_parallel"
proof 
  show " \<And>P Q. P \<noteq> Q \<Longrightarrow>
           P \<in> A4Points \<Longrightarrow>
           Q \<in> A4Points \<Longrightarrow>
           A4join P Q
           \<in> A4Lines \<and>
           A4meets P
            (A4join P Q) \<and>
           A4meets Q
            (A4join P Q)" using A4a1a by auto
  show " \<And>P l. P \<in> A4Points \<Longrightarrow>
           l \<in> A4Lines \<Longrightarrow>
           A4find_parallel l P
           \<in> A4Lines" using A4a2a by auto
  show "\<And>P Q m.
       P \<noteq> Q \<Longrightarrow>
       P \<in> A4Points \<Longrightarrow>
       Q \<in> A4Points \<Longrightarrow>
       A4meets P m \<Longrightarrow>
       A4meets Q m \<Longrightarrow>
       m = A4join P Q" 
    using  A4a1b  by auto

  show "\<And>P l. P \<in> A4Points \<Longrightarrow>
           l \<in> A4Lines \<Longrightarrow>
           affine_plane_data.parallel
            A4Points A4Lines
            A4meets
            (A4find_parallel l
              P)
            l" using A4a2a A4a2b by auto
  show " \<And>P l. P \<in> A4Points \<Longrightarrow>
           l \<in> A4Lines \<Longrightarrow>
           A4meets P
            (A4find_parallel l
              P)"  using A4a2c by blast
  show "\<exists>P Q R.
       P \<in> A4Points \<and>
       Q \<in> A4Points \<and>
       R \<in> A4Points \<and>
       P \<noteq> Q \<and>
       P \<noteq> R \<and>
       Q \<noteq> R \<and>
       \<not> affine_plane_data.collinear
           A4Points A4Lines
           A4meets P Q R" using A4a3 by auto
qed

end

