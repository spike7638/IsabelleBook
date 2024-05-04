theory Projective_Basics
  imports Complex_Main 
begin

locale projective_plane_data =
  fixes Points :: "'p set" and Lines :: "'l set" and meets :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  fixes join:: "'p \<Rightarrow> 'p \<Rightarrow> 'l"
begin

definition point_pencil::"'p \<Rightarrow> 'l set" where
"point_pencil P = { n::'l . meets P n}"

fun collinear :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
    where "collinear A B C = (if A \<in> Points \<and> B \<in> Points \<and> C \<in> Points 
  then (\<exists> l. l \<in> Lines \<and> meets A l \<and> meets B l \<and> meets C l) else undefined)"
end

locale projective_plane =
    projective_plane_data  +
    assumes
    p1a: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points\<rbrakk> \<Longrightarrow> join P Q \<in> Lines \<and> meets P (join P Q)  \<and> meets Q (join P Q)" and
    p1b: "\<lbrakk>P \<noteq> Q; P \<in> Points; Q \<in> Points; meets P m; meets Q m\<rbrakk> \<Longrightarrow> m = join P Q" and
    p2: "\<lbrakk> n \<in> lines; l \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P . meets P n \<and> meets P l" and
    p3: "\<exists>P Q R. P \<in> Points \<and> Q \<in> Points \<and> R \<in> Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> (collinear P Q R)" and
    p4: "\<lbrakk>n \<in> Lines\<rbrakk> \<Longrightarrow> \<exists> P Q R .  P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> meets P n \<and> meets Q n \<and> meets R n" 
begin

lemma join_symmetric: 
  fixes P Q
  assumes "P \<in> Points"
  assumes "Q \<in> Points"
  assumes "P \<noteq> Q" 
  shows "join P Q = join Q P" 
proof -
  have 2: "meets P (join Q P)" using assms p1a by auto
  have 3: "meets Q (join Q P)" using assms p1a by auto
  have "join Q P = join P Q" using assms 2 3  p1b by blast
  then show ?thesis by auto
qed


fun (in projective_plane_data) liesOn :: "'p \<Rightarrow> 'l \<Rightarrow> bool" (infix "liesOn" 50) where
  "P liesOn m = (if P  \<in> Points \<and> (m \<in> Lines) then meets P m  else undefined)"

fun  (in projective_plane_data) contains :: "'l \<Rightarrow> 'p \<Rightarrow> bool" (infix "contains" 50) where
  "m contains P = (P liesOn m)"

theorem join_containsL:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "P liesOn (join P Q)"
proof -
  have 0: "meets P (join P Q)" using p1a assms by blast
  have 1: "(join P Q)  \<in> Lines" using p1a assms by blast
  show ?thesis by (simp add: "0" "1" assms)
qed                                                                

theorem join_containsL2:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "meets P (join P Q)"
proof -
  show ?thesis using p1a assms by blast
qed                                                                

theorem join_containsR:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "Q liesOn (join P Q)"
proof -
  have 0: "meets Q (join P Q)" using p1a assms by blast
  have 1: "(join P Q)  \<in> Lines" using p1a assms by blast
  show ?thesis by (simp add: "0" "1" assms)
qed                                                                

theorem join_containsR2:
  fixes P Q
  assumes "P \<noteq> Q"
  assumes "P  \<in> Points"
  assumes "Q  \<in> Points"                                          
  shows "meets Q (join P Q)"
proof -
 show ?thesis  using p1a assms by blast
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
  have 2: "(join Q P) = (join P Q)" using "0" "1" p1b assms by blast 
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

(* .to prove: two distinct lines meet in exactly one point. Define the crossing function using THE ? *)
(* For any line, there's a point not on it [reason: one of P, Q, R from P3] *)
(* given two distinct lines, n and k, there are two points of n not on k.*)
(* For any (distinct) points, there's a line passing through neither [why?] (also true if points are same, of course) *)
(* For any (distinct) lines, there's a point not on either [why] (also true if lines are same, of course) *)
(* for any two (distinct) lines, there's a line distinct from both [also true if original lines 
are NOT distinct *)
(* any two lines are in 1-1 correspondence (projectivity from point not on either line) *)
(* any two point-pencils are in 1-1 correspondence *)
(* Projectivization of an affine plane is a projective plane *)
(* dual of a projective plane is a projective plane *)

theorem lines_intersect_in_one_point:
  fixes k n P Q
  assumes "k \<in> Lines" and "n \<in> Lines"
  assumes "n \<noteq> k"
  assumes "P \<in> Points" and "Q \<in> Points"
  assumes "meets P k" and "meets P n"
  assumes "meets Q k" and "meets Q n"
  shows "P = Q"
proof (rule ccontr)
  assume a: "\<not> (P = Q)"
  have 0:"k = join P Q" using assms a  p1b by auto
  have 1:"n = join P Q" using assms(4, 5,7,9) a p1b by auto
  have 2: "n = k" using 0 1 by auto
  show "False" using 2 assms(3) by auto
qed
  

 


end
