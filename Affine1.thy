theory Affine1
  imports Complex_Main 
begin

locale affine_plane_data =
  fixes Points :: "'p set" and Lines :: "'l set" and meets :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes join:: "'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel:: "'l \<Rightarrow> 'p \<Rightarrow> 'l"
begin
  fun parallel :: "'l \<Rightarrow> 'l \<Rightarrow> bool" (infix "||" 50) where
  "l || m = (if (l \<in> Lines \<and> m \<in> Lines) 
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

fun A4find_parallel::"a4pt set \<Rightarrow> a4pt \<Rightarrow> a4pt set"  where
"A4find_parallel m T = (if T \<in> m then m else (A4Points - m))"

fun A4meets::"a4pt \<Rightarrow> a4pt set \<Rightarrow> bool" where
"A4meets x m = ((m \<in> A4Lines) \<and> (x \<in> m))"

thm A4meets.simps
thm A4join.simps 
thm A4Points_def


theorem
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and" Q \<in> A4Points"
shows "A4join P Q \<in> A4Lines"
proof (cases P)
  case zz:Pa
  then show ?thesis 
  proof (cases Q)
    case ww:Pa
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  next
    case ww:Qa
    have rr: "A4join P Q = A4PQ" using zz ww A4PQ_def by simp
    then show ?thesis using rr A4Lines_def by blast
  next
    case ww:Ra
    have rr: "A4join P Q = A4PR" using zz ww A4PR_def by simp
    then show ?thesis using rr A4Lines_def by blast
  next
    case ww:Sa
    have rr: "A4join P Q = A4PS" using zz ww A4PS_def by simp
    then show ?thesis using rr A4Lines_def by blast
  qed
next
  case zz:Qa
  then show ?thesis 
  proof (cases Q)
    case ww:Pa
    have rr: "A4join P Q = A4PQ" using zz ww A4PQ_def by auto
    then show ?thesis using rr A4Lines_def by blast
  next
    case ww:Qa
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  next
    case ww:Ra
    have rr: "A4join P Q = A4QR" using zz ww A4QR_def by auto
    then show ?thesis using rr A4Lines_def by blast
  next
    case ww:Sa
    have rr: "A4join P Q = A4QS" using zz ww A4QS_def by simp
    then show ?thesis using rr A4Lines_def by blast
  qed
next
  case zz:Ra
  then show ?thesis 
  proof (cases Q)
    case ww:Pa
    have rr: "A4join P Q = A4PR" using zz ww A4PR_def by auto
    then show ?thesis using rr A4Lines_def by blast
  next
    case ww:Qa
    have rr: "A4join P Q = A4QR" using zz ww A4QR_def by auto
    then show ?thesis using rr A4Lines_def by blast
  next
    case ww:Ra
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  next
    case ww:Sa
    have rr: "A4join P Q = A4RS" using zz ww A4RS_def by simp
    then show ?thesis using rr A4Lines_def by blast
  qed
next
  case zz:Sa
  then show ?thesis 
  proof (cases Q)
    case ww:Pa
    have rr: "A4join P Q = A4PS" using zz ww A4PS_def by auto
    then show ?thesis using rr A4Lines_def by blast
  next
    case ww:Qa
    have rr: "A4join P Q = A4QS" using zz ww A4QS_def by auto
    then show ?thesis using rr A4Lines_def by blast
  next
    case ww:Ra
    have rr: "A4join P Q = A4RS" using zz ww A4RS_def by auto
    then show ?thesis using rr A4Lines_def by blast
  next
    case ww:Sa
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  qed
qed

theorem PinPQ1:
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and" Q \<in> A4Points"
shows "P \<in> A4join P Q"
proof (cases P)
  case zz:Pa
  then show ?thesis 
  proof (cases Q)
    case ww:Pa
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  next
    case ww:Qa
    then show ?thesis using zz  A4PQ_def by auto
  next
    case ww:Ra
    then show ?thesis using zz  A4PR_def by auto
  next
    case ww:Sa
    then show ?thesis using zz  A4PS_def by auto
  qed
next
  case zz:Qa
  then show ?thesis 
  proof (cases Q)
    case ww:Qa
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  next
    case ww:Pa
    then show ?thesis using zz  by auto
  next
    case ww:Ra
    then show ?thesis using zz  by auto
  next
    case ww:Sa
    then show ?thesis using zz by auto
  qed
next
  case zz:Ra
  then show ?thesis 
  proof (cases Q)
    case ww:Ra
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  next
    case ww:Pa
    then show ?thesis using zz  by auto
  next
    case ww:Qa
    then show ?thesis using zz  by auto
  next
    case ww:Sa
    then show ?thesis using zz by auto
  qed
next
  case zz:Sa
  then show ?thesis 
  proof (cases Q)
    case ww:Sa
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  next
    case ww:Pa
    then show ?thesis using zz  by auto
  next
    case ww:Qa
    then show ?thesis using zz  by auto
  next
    case ww:Ra
    then show ?thesis using zz by auto
  qed
qed

theorem QinPQ1:
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and" Q \<in> A4Points"
shows "Q \<in> A4join P Q"
proof (cases P)
  case zz:Pa
  then show ?thesis 
  proof (cases Q)
    case ww:Pa
    have "False" using zz ww assms by blast 
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
(* alternate: skip c2; say "have False using c1 assms by blast" 
Simpler still: skip c1, c2, and write     
have "False" using zz ww assms by blast 
or even simpler:
    show ?thesis using zz ww assms by blast 
*)
    thus ?thesis by blast
  next
    case ww:Qa
    then show ?thesis using zz A4PQ_def by auto
  next
    case ww:Ra
    then show ?thesis using zz  A4PR_def by auto
  next
    case ww:Sa
    then show ?thesis using zz  A4PS_def by auto
  qed
next
  case zz:Qa
  then show ?thesis 
  proof (cases Q)
    case ww:Qa
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  next
    case ww:Pa
    then show ?thesis using zz  by auto
  next
    case ww:Ra
    then show ?thesis using zz  by auto
  next
    case ww:Sa
    then show ?thesis using zz by auto
  qed
next
  case zz:Ra
  then show ?thesis 
  proof (cases Q)
    case ww:Ra
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  next
    case ww:Pa
    then show ?thesis using zz  by auto
  next
    case ww:Qa
    then show ?thesis using zz  by auto
  next
    case ww:Sa
    then show ?thesis using zz by auto
  qed
next
  case zz:Sa
  then show ?thesis 
  proof (cases Q)
    case ww:Sa
    have c1: "P = Q" using zz ww by simp
    also have  c2: "P \<noteq> Q" using assms by simp
    have "False" using c1 c2 by blast 
    thus ?thesis by blast
  next
    case ww:Pa
    then show ?thesis using zz  by auto
  next
    case ww:Qa
    then show ?thesis using zz  by auto
  next
    case ww:Ra
    then show ?thesis using zz by auto
  qed
qed

theorem
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and" Q \<in> A4Points"
shows "A4meets P (A4join P Q)"
  using assms by auto

theorem
  fixes P Q
  assumes   "P \<noteq> Q" and
 " P \<in> A4Points"  and" Q \<in> A4Points"
shows "A4meets Q (A4join P Q)"
proof -
  show ?thesis using assms by auto
qed
lemma not_four_and:
  fixes p1 p2 p3 p4
  assumes "\<not> (p1 \<and> p2 \<and> p3 \<and> p4)"
  shows   "(\<not> p1) \<or> (\<not> p2) \<or> (\<not> p3) \<or> (\<not> p4)"
  using assms by blast

theorem A4affine_plane: "affine_plane A4Points A4Lines A4meets A4join A4find_parallel"
proof 
  show "  \<exists>P Q R.
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
  have "\<not> (affine_plane_data.collinear
           A4Points A4Lines A4meets Pa Qa Ra)" 

  proof -
    have 0: "affine_plane_data.collinear A4Points A4Lines A4meets Pa Qa Ra = 
     (if Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points 
    then (\<exists> l. l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l \<and> A4meets Ra l) else undefined)"
      by (simp add: affine_plane_data.collinear.simps) 
    have 1: "Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points" using u0 u1 u2 by auto
    have 2: "affine_plane_data.collinear A4Points A4Lines A4meets Pa Qa Ra = 
     (\<exists> l. l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l \<and> A4meets Ra l)" using 0 1 by auto
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
    have 7: "(A4meets Pa l) = (l = {Pa, Qa}) \<or> (l = {Pa, Ra}) \<or> (l = {Pa, Sa})" using A4meets.simps
      by (metis A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def a4pt.simps(5) d1 empty_iff insert_iff)  
    have 8: "(A4meets Qa l) = (l = {Pa, Qa}) \<or> (l = {Qa, Ra}) \<or> (l = {Qa, Sa})" using A4meets.simps
      by (metis A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def a4pt.simps(9) empty_iff insert_iff) 
    have 9: "(A4meets Ra l) = (l = {Pa, Ra}) \<or> (l = {Qa, Ra}) \<or> (l = {Ra, Sa})"
      by (metis A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4meets.simps d1 empty_iff insert_iff)
    have 10: "((A4meets Pa l) \<and> (A4meets Qa l)) =  (l = {Pa, Qa})" using 7 8 by auto
    have 11: "((A4meets Pa l) \<and> (A4meets Qa l) \<and> (A4meets Ra l)) = False" using 9 10 by auto
    then show ?thesis
      by (metis "0" A4Lines_def A4PQ_def A4PR_def A4PS_def A4QR_def A4QS_def A4RS_def A4meets.elims(2) d0 d1 d2 empty_iff insert_iff u0 u1 u2)
  qed
  show ?thesis
    using \<open>\<not> affine_plane_data.collinear A4Points A4Lines A4meets Pa Qa Ra\<close> u0 u1 u2 by blast
qed
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
    A4join P Q \<in> A4Lines" using a0 


      
(*
  proof -
    have step0: "\<not> (if Pa \<in> A4Points \<and> Qa \<in> A4Points \<and> Ra \<in> A4Points 
  then (\<exists> l. l \<in> A4Lines \<and> A4meets Pa l \<and> A4meets Qa l \<and> A4meets Ra l) else undefined)" sorry
    show ?thesis using step0 by try0
*)
(*
  show " \<And>P Q. P \<noteq> Q \<Longrightarrow>
           P \<in> A4Points \<Longrightarrow>
           Q \<in> A4Points \<Longrightarrow>
           A4join P Q \<in> A4Lines \<and>
           A4meets P (A4join P Q) \<and>
           A4meets Q (A4join P Q)" 
  proof (intro conjI)
*)



(*

fixes join:: "'p \<Rightarrow> 'p \<Rightarrow> 'l"
  fixes find_parallel:: "'l \<Rightarrow> 'p \<Rightarrow> 'l"
*)

notepad
begin
end

datatype a2pt = A2Point "real" "real"
datatype a2ln = A2Ordinary "real" "real" 
  | A2Vertical "real"



notepad
begin

  text "Ordinary m b represents the line y = mx+b; Vertical xo is the line x = xo. With this in 
mind, we define the  `meets' operation for this purported plane, using cases for the definition."
  text\<open> There's a problem here, though: for A2Ordinary, we have to have the "m" term be nonzero,
so we need to define a set Lines; the set Points is just all a2pts" 
  fun a2meets :: "a2pt \<Rightarrow> a2ln \<Rightarrow> bool" where
    "a2meets (A2Point x y) (A2Ordinary m b) = (y = m*x + b)" |
    "a2meets (A2Point x y) (A2Vertical xi) = (x = xi)"\<close>

  definition a2parallel:: "a2ln  \<Rightarrow> a2ln \<Rightarrow> bool" (infix "a2||" 50)
      where "l a2|| m \<longleftrightarrow> (l = m \<or>  (\<forall> P. (\<not> a2meets P l)  \<or> (\<not>a2meets P m)))"
  text\<open> Notice that I've written the definition of parallel for the euclidean affine plane
as a forall rather than exists. I think this might make things easier.\<close>
  text\<open>Now we'll write some small lemmas, basically establishing the three axioms.\<close>
  text\<open> I'm going to venture into a new style of writing theorems and proofs, one that's
particularly applicable when you're showing something exists by constructing it. Here is 
an example in the case of real numbers: if $r < s$, then there's a real number strictly between
them. We could write this as ``$r < s$ shows that there is a $t$ . ($(r < t)$ and $(t < s)$)'' (although it turns out we'd have
to start with ``\texttt{(r::real) < s ...}'' to tell Isar not to assume that r is a natural number -- after all, 
this is one of those cases where type-inference has no idea whether ``$<$'' means less-than on the reals,
or the integers, or the natural numbers, or ...)

Anyhow, in this new style, we would type the theorem like this:

\begin{lstlisting}[language=Isabelle]{}
theorem mid:
  fixes r :: real
  assumes lt : "r < s"
  shows "\<exists>t. r < t \<and> t < s"
proof
  let ?t = "(r + s) / 2"
  from lt show "r < ?t \<and> ?t < s" by simp
qed
\end{lstlisting}
\<close>

  text\<open>The nice thing about this style is that it takes care of "fix"ing things in the theorem statement,
and takes care of assuming the antecedent (which we always end up doing in the proof anyhow), and
then makes clear what we're going to actually show. We will treat this as a pattern henceforth.

A note about naming: Everything related to real-affine-2-space will be written with a prefix
``A2''. When we want to state axiom 3 for A2, we'll write ``A2\_a3''. Sometimes we'll need some preliminary
results, and we'll append an ``a'' or ``b'' or ``c'', etc., before stating the main result. \caleb \<close>

theorem A2_a1a: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q"
  shows "\<exists> ls . a2meets P ls \<and> a2meets Q ls"
proof (cases P, cases Q)
  fix x0 y0 assume P: "P = (A2Point x0 y0)"
  fix x1 y1 assume Q: "Q = (A2Point x1 y1)" 
  show ?thesis
  proof (cases "(x0 = x1)")

    case True (* Case where x0 = x1 *)
    let ?ll = "A2Vertical x0"
    have m1:  "a2meets P ?ll" using P by simp
    have m2:  "a2meets Q ?ll" using Q True by simp
    have "a2meets P ?ll \<and> a2meets Q ?ll" using m1 m2 by auto
    thus ?thesis by auto
  
  next
    case False (* Case where x0 \<noteq> x1*) 
    let ?rise = "y1 - y0"
    let ?run  = "x1 - x0"
    let ?m    = "?rise/?run"
    let ?b    = "y0 - ?m*x0"
    let ?ll   = "A2Ordinary ?m ?b"

    have m3: "a2meets P ?ll" using P by simp
    have m4: "a2meets Q ?ll"
    proof -
      have s0: "y1*?run/?run = ?m*x1 + (y0 * ?run/?run - ?m*x0)"
        by argo
      have s1: "y1 = ?m*x1 + ?b" using s0 False by auto
      thus ?thesis using s1 Q a2meets.simps(1) by blast

    qed
    show ?thesis using m3 m4 by blast
  qed
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
  fixes m
  assumes pq: "P \<noteq> Q"
  assumes pl : "a2meets P l"
  assumes ql : "a2meets Q l"
  assumes pm : "a2meets P m"
  assumes qm : "a2meets Q m"
  shows "l = m"

proof (cases P, cases Q)
    fix x0 y0 assume P: "P = (A2Point x0 y0)"
    fix x1 y1 assume Q: "Q = (A2Point x1 y1)" 
    show ?thesis
    proof (cases "(x0 = x1)")
      case True
      then show ?thesis 
        by (smt P Q a2ln.inject(1) a2meets.elims(2) a2meets.simps(2) pl pm pq ql qm)
    next
      case False
      then show ?thesis
        by (smt P Q a2ln.inject(1) a2meets.elims(2) a2meets.simps(2) a2pt.inject crossproduct_noteq pl pm ql qm)
    qed
  qed


lemma A2_a1:
  fixes P :: a2pt
  fixes Q
  assumes pq: "P \<noteq> Q"
  shows "\<exists>! ls . a2meets P ls \<and> a2meets Q ls"
proof -
  show ?thesis using pq A2_a1a A2_a1b by auto
qed

text \<open>\done Whew! We've proved axiom 1 for the real affine plane. On to Axiom 2. This one's 
a little trickier because we're proving a conjunction. \caleb\<close>
lemma A2_a2a (*existence*):
  fixes P :: a2pt 
  fixes l 
  assumes "\<not> a2meets P l"
  shows  "\<exists>k. a2meets P k \<and> l a2|| k"

proof (cases P)
  fix x0 y0 assume P: "P = (A2Point x0 y0)"
  have existence: "\<exists>m. l a2|| m \<and> a2meets P m"
  proof (cases l)
    case (A2Vertical x1)
    obtain m where mvert: "m = (A2Vertical x0)" 
      by simp
    have lparallelm: "a2parallel l m"
      by (metis A2Vertical a2meets.simps(2) a2parallel_def a2pt.exhaust mvert)
    have Ponm: "a2meets P m"
      by (simp add: P mvert)
    then show ?thesis
      using lparallelm by auto
  next
    case (A2Ordinary slope intercept)
    obtain intercept2 where a: "intercept2 = y0 - slope * x0" 
      by simp
    obtain line2 where eq: "line2 = (A2Ordinary slope intercept2)" 
      by simp
    have PonLine2: "a2meets P line2"
      by (simp add: P a eq)
    then show ?thesis
      by (smt A2Ordinary a2meets.elims(2) a2meets.simps(1) a2parallel_def eq) 
  qed
  thus ?thesis
    by auto 
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

lemma A2_parallel_1: 
  fixes l
  fixes m
  assumes lo: "l = A2Vertical x2 "
  assumes lm_parr : "l a2|| m"
  shows "\<exists>s2. m = A2Vertical s2 "

  by (metis A2_basics_1 a2ln.exhaust lm_parr lo)
    


text\<open> Let's do the other half of that: if l is ordinary, and m is parallel, then m is ordinary \<close>
lemma A2_parallel_2: 
  fixes l
  fixes m
  assumes lo: "l = A2Ordinary s1 b1 "
  assumes lm_parr : "l a2|| m"
  shows "\<exists>s2 b2. m = A2Ordinary s2 b2 "
  by (metis A2_basics_1 a2ln.exhaust a2parallel_def lm_parr lo)
  

text\<open> And a third half: if l and m are parallel and ordinary, them their slopes are the same \<close>
lemma A2_parallel_3: 
  fixes l
  fixes m
  assumes lo: "l = A2Ordinary s1 b1 "
  assumes mo: "m = A2Ordinary s2 b2 "
  assumes lm: "l a2|| m"

  shows "s1 = s2"
  using A2_basics_2 lm lo mo by blast 
 

text\<open>\done  Recall that axiom 2 states that there's a unique m 
through P, parallel to l.    
We'll phrase that just the way we did A1.a1b: \caleb \seiji\<close>
(* a2: "\<not> meets P l \<Longrightarrow> \<exists>!m. l || m \<and> meets P m" *)

lemma A2_a2b: 
  fixes P
  fixes l
  fixes m
  fixes k
  assumes pl : "\<not> a2meets P l"
  assumes pm : "a2meets P m"
  assumes pk : "a2meets P k"
  assumes lm_parr : "l a2|| m"
  assumes lk_parr : "l a2|| k"
  shows "m = k"
proof (cases m)
  case (A2Ordinary x11 x12)
  obtain xl yl where l_ord: "l = (A2Ordinary xl yl)"
    by (metis A2Ordinary A2_basics_1 a2meets.elims(3) lm_parr pl)
  obtain xk yk where k_ord: "k = (A2Ordinary xk yk)"
    using A2_parallel_2 l_ord lk_parr by blast
  have equality: "xl = xk \<and> x11 = xl"
    using A2Ordinary A2_basics_2 k_ord l_ord lk_parr lm_parr by force 
  have m_par_k: "m a2|| k"
    using A2Ordinary a2meets.elims(2) a2parallel_def equality k_ord by force
  then show ?thesis
    using a2parallel_def pk pm by blast
next
  case (A2Vertical x2)
  obtain xl where l_vert: "l = (A2Vertical xl)"
    by (metis A2Vertical A2_parallel_2 a2ln.distinct(1) a2meets.elims(3) lm_parr pl)
  obtain xk where k_vert: "k = (A2Vertical xk)"
    using A2_parallel_1 l_vert lk_parr by blast
  have equal: "xk = x2"
    by (metis A2Vertical a2meets.elims(2) a2meets.simps(2) k_vert pk pm)
  then show ?thesis
    using A2Vertical k_vert by auto
qed
lemma A2_a2: 
  fixes P
  fixes l
  assumes "\<not> a2meets P l"
  shows "\<exists>! m. a2meets P m \<and> m a2|| l"
  by (smt A2_a2a A2_a2b a2parallel_def)



lemma A2_a3:
  shows  "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> (\<nexists> m. a2meets P m \<and> a2meets Q m \<and> a2meets R m)"
proof -
  obtain P where P: "P = (A2Point 0 0)" by simp
  obtain Q where Q: "Q = (A2Point 1 0)" by simp
  obtain R where R: "R = (A2Point 0 1)" by simp

  have "(\<nexists> m. a2meets P m \<and> a2meets Q m \<and> a2meets R m)"
    by (metis A2_a1b P Q R a2meets.simps(2) a2pt.inject zero_neq_one)

  thus ?thesis
    by (metis (full_types) A2_a1 A2_a2)

qed
text\<open>\done \done\<close>

lemma A2_a3x:
  shows "\<not> (\<exists> m. a2meets (A2Point 0 0)  m \<and> a2meets (A2Point 0 1) m \<and> a2meets (A2Point 1 0) m)"

  by (metis A2_a1b a2meets.simps(1) a2pt.inject add.right_neutral mult_zero_left zero_neq_one)
  

lemma A2_a3y: (* alternative formulation -- harder to read, easier to prove *)
  fixes m
  assumes "a2meets (A2Point 0 0) m"
  assumes "a2meets (A2Point 0 1) m"
  shows "\<not> (a2meets (A2Point 1 0) m)"
  using A2_a3x assms(1) assms(2) by blast

lemma A2_a3z1: (* alternative formulation -- harder to read, easier to prove *)
  fixes m
  assumes "a2meets (A2Point 0 0) m"
  assumes "a2meets (A2Point 0 1) m"
  shows "m = (A2Vertical 0)"
  by (smt a2ln.inject(1) a2meets.elims(2) a2pt.inject assms(1) assms(2))

text\<open> At this point we've established that the Cartesian Plane satisfies Cartesian 
versions of the three axioms, etc., but it'd be nice to be able to say that as
a *structure*, it matches the Isabelle "locale" that we defined. \caleb \seiji 
\<close>

theorem A2_affine: "affine_plane UNIV UNIV a2meets"
  unfolding affine_plane_def
  apply (intro conjI)
  subgoal using A2_a1
    by simp
  subgoal
    by (smt A2_a2a A2_a2b a2parallel_def affine_plane_data.parallel.simps iso_tuple_UNIV_I) 
  apply (simp add: affine_plane_data.collinear.simps)
  using A2_a3 by auto



end

(* An exaple of showing that something is of the type required in a locale; this is what I'll use to 
show that R^2 is actually an affine plane. 

locale equivalence =
fixes S (structure)
assumes refl [simp, intro]: "x \<in> carrier S =\<Rightarrow> x .= x"
and sym [sym]: "[[ x .= y; x \<in> carrier S; y \<in> carrier S ]] =\<Rightarrow> y .=
x"
and trans [trans]:
"[[ x .= y; y .= z; x \<in> carrier S; y \<in> carrier S; z \<in> carrier S ]]
=\<Rightarrow> x .= z"

lemma equivalenceI:
fixes P :: "’a \<Rightarrow> ’a \<Rightarrow> bool" and E :: "’a set"
assumes refl: "V
x. [[ x \<in> E ]] =\<Rightarrow> P x x"
and sym: "V
x y. [[ x \<in> E; y \<in> E ]] =\<Rightarrow> P x y =\<Rightarrow> P y x"
and trans: "V
x y z. [[ x \<in> E; y \<in> E; z \<in> E ]] =\<Rightarrow> P x y =\<Rightarrow> P y z
=\<Rightarrow> P x z"
shows "equivalence (| carrier = E, eq = P |)"
unfolding equivalence_def using assms
by (metis eq_object.select_convs(1) partial_object.select_convs(1))
*)

(* In our case, we need to construct an affine plane, i.e., we'll write
shows "affine_plane \<lparr>  Points Lines meets join find_parallel \<rparr> 

Points will be all of R^2
Lines will be ... how to represent them uniquely?
meets is easy: a dot-product is zero
join is easy: take a cross-product
find_parallel: adjust the constant term in the line equation to make P lie on it; then ajust
the numbers to make them a valid line-representation.
*)
