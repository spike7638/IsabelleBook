theory Affine_Basics
  imports Complex_Main 
begin

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

definition point_pencil::"'p \<Rightarrow> 'l set" where
"point_pencil P = { n::'l . meets P n}"

definition line_pencil::"'l \<Rightarrow> 'l set" where
"line_pencil k = { n::'l . n || k}"

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
end