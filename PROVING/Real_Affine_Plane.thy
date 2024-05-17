theory Real_Affine_Plane
  imports Complex_Main Affine_Basics
begin

(* A2Ordinary B C is the line x + By + C = 0 *)
(* Describe lines by equations Ax  + By + C = 0 where either A = 1 or (A = 0 and B = 1) *)
datatype a2pt = A2Point "real" "real"
datatype a2ln = A2Ordinary "real" "real" (* A2Ordinary B C is the line 1x + By + C = 0 *)
  | A2Horizontal "real" (* A2Horizontal C is the line 0x + 1y + C = 0 *)

definition "(A2Points::a2pt set) = UNIV"
definition "(A2Lines::a2ln set) = UNIV"

fun A2meets:: "a2pt \<Rightarrow> a2ln \<Rightarrow> bool" where
"A2meets (A2Point x y) (A2Ordinary B C) = (x + B * y + C = 0)" |
"A2meets (A2Point x y) (A2Horizontal  C) = (y + C = 0)"

fun A2join:: "a2pt \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"A2join (A2Point x1 y1) (A2Point x2 y2) = 
  (if (y1 = y2) then (if (x1 = x2) then undefined else (A2Horizontal (-y1)))
    else (A2Ordinary ((x2-x1)/(y1-y2)) ((x1*y2-x2*y1)/(y1-y2))))" 
fun A2find_parallel::"a2ln \<Rightarrow> a2pt \<Rightarrow> a2ln" where
"A2find_parallel  (A2Horizontal C) (A2Point x1 y1) = A2Horizontal (-y1)" | 
"A2find_parallel (A2Ordinary B C) (A2Point x1 y1) = A2Ordinary B (-x1 - B * y1)" 

lemma hMeets:
  shows "A2meets (A2Point x y) (A2Horizontal C) \<Longrightarrow> C = -y"
  by simp

theorem  A2a1a:
  fixes P Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  shows  "A2join P Q \<in> A2Lines \<and> A2meets P (A2join P Q)  \<and> A2meets Q (A2join P Q)"
proof -
  obtain x1 y1 where  "P  = A2Point x1 y1"
    using a2pt.exhaust by blast 
  obtain x2 y2 where  "Q  = A2Point x2 y2" using a2pt.exhaust by blast
  have d: "x1 \<noteq> x2 \<or> y1 \<noteq> y2" 
    using assms \<open>P = A2Point x1 y1\<close> \<open>Q = A2Point x2 y2\<close> by blast 
  show "A2join P Q \<in> A2Lines \<and> A2meets P (A2join P Q) \<and> A2meets Q (A2join P Q)" 
  proof (cases "y1 = y2")
    case True
    have "x1 \<noteq> x2" using d True by blast
    have u1: "A2join P Q = A2Horizontal (-y1)"
      by (simp add: True \<open>P = A2Point x1 y1\<close> \<open>Q = A2Point x2 y2\<close> \<open>x1 \<noteq> x2\<close>)
    have u2: "A2meets P (A2join P Q)" 
      using u1 \<open>P = A2Point x1 y1\<close> by auto
    have u3: "A2meets Q (A2join P Q)" 
      using u1 \<open>Q = A2Point x2 y2\<close> True  by auto

    then show ?thesis using u1 u2 u3 
      by (simp add: A2Lines_def) 
  next
    case False
    have u1: "A2join P Q = A2Ordinary ((x2-x1)/(y1-y2)) ((x1*y2-x2*y1)/(y1-y2))"
      using False \<open>P = A2Point x1 y1\<close> \<open>Q = A2Point x2 y2\<close> by force
    have u2: "A2meets P (A2join P Q)" 
    proof -
      have 1: "A2meets P (A2join P Q) = 
      A2meets (A2Point x1 y1) (A2Ordinary ((x2-x1)/(y1-y2)) ((x1*y2-x2*y1)/(y1-y2)))" 
        using u1 \<open>P = A2Point x1 y1\<close> False
        using A2join.simps \<open>Q = A2Point x2 y2\<close> by presburger 
      also have 2: "... = (x1 + ((x2-x1)/(y1-y2)) * y1 + ((x1*y2-x2*y1)/(y1-y2)) = 0)" using A2meets.simps by auto
      also have 3: "... = (x1 + ((x2-x1)*y1) /(y1-y2) + (x1*y2-x2*y1)/(y1-y2) = 0)" using A2meets.simps by auto
      also have 4: "... = (x1 + (((x2-x1)*y1)  + (x1*y2-x2*y1))/(y1-y2) = 0)" using False
        by (simp add: add_divide_distrib group_cancel.add1)
      also have 5: "... = ( (((x2-x1)*y1)  + (x1*y2-x2*y1))/(y1-y2) = -x1)"
        by fastforce
      also have 6: "... = ( ((x2*y1 -x1*y1)  + x1*y2-x2*y1)/(y1-y2) = -x1)"
        by (simp add: left_diff_distrib) 
      also have 7: "... = ( ( -x1*y1  + x1*y2)/(y1-y2) = -x1)" by (simp add:algebra_simps)
      also have 8: "... = ( ( -x1*y1  + x1*y2) = -x1*(y1-y2))" 
        using False  by (simp add: nonzero_divide_eq_eq)
      also have 9: "... = ( ( -x1*y1  + x1*y2) = -x1*y1+x1*y2)" by (simp add:algebra_simps)
      also have 10: "... = ( True)" by (simp add:algebra_simps)
      thus ?thesis
        using calculation by auto
    qed
    have u3: "A2meets Q (A2join P Q)" 
    proof -
      have 1: "A2meets Q (A2join P Q) = 
      A2meets (A2Point x2 y2) (A2Ordinary ((x2-x1)/(y1-y2)) ((x1*y2-x2*y1)/(y1-y2)))" 
        using u1 \<open>Q = A2Point x2 y2\<close> False A2join.simps \<open>P = A2Point x1 y1\<close> by presburger 
      also have 2: "... = (x2 + ((x2-x1)/(y1-y2)) * y2 + ((x1*y2-x2*y1)/(y1-y2)) = 0)" using A2meets.simps by auto
      also have 3: "... = (x2 + ((x2-x1)*y2) /(y1-y2) + (x1*y2-x2*y1)/(y1-y2) = 0)" using A2meets.simps by auto
      also have 4: "... = (x2 + (((x2-x1)*y2)  + (x1*y2-x2*y1))/(y1-y2) = 0)" using False
        by (simp add: add_divide_distrib group_cancel.add1)
      also have 5: "... = ( (((x2-x1)*y2)  + (x1*y2-x2*y1))/(y1-y2) = -x2)"
        by fastforce
      also have 6: "... = ( ((x2*y2 -x1*y2)  + x1*y2-x2*y1)/(y1-y2) = -x2)"
        by (simp add: left_diff_distrib) 
      also have 7: "... = ( ( x2*y2  - x2*y1)/(y1-y2) = -x2)" by (simp add:algebra_simps)
      also have 8: "... = ( ( x2*y2  - x2*y1) = -x2*(y1-y2))" 
        using False  by (simp add: nonzero_divide_eq_eq)
      also have 9: "... = ( True )" by (simp add:algebra_simps)
      then show ?thesis using calculation by auto
    qed
    show ?thesis  using u1 u2 u3
      using A2Lines_def by blast
  qed
qed

theorem A2a1b:
  fixes P Q
  assumes "P \<noteq> Q" and "P \<in> A2Points" and "Q \<in> A2Points"
  assumes "A2meets P m" and "A2meets Q m"
  shows  "m = A2join P Q"
proof -
  obtain x1 y1 where  pf: "P  = A2Point x1 y1"
    using a2pt.exhaust by blast 
  obtain x2 y2 where  qf: "Q  = A2Point x2 y2" using a2pt.exhaust by blast
  have d: "x1 \<noteq> x2 \<or> y1 \<noteq> y2" 
    using assms \<open>P = A2Point x1 y1\<close> \<open>Q = A2Point x2 y2\<close> by blast 
  have u1: "A2join P Q \<in> A2Lines" using assms A2a1a by blast
  have u2: "A2meets P (A2join P Q)" using assms A2a1a by blast 
  have u3: "A2meets Q (A2join P Q)" using assms A2a1a by blast

  show ?thesis
  proof(cases "y1 = y2")
    case True
    have e: "x1 \<noteq> x2" using d True by blast
    have u1: "A2join P Q = A2Horizontal (-y1)"
      by (simp add: True \<open>P = A2Point x1 y1\<close> \<open>Q = A2Point x2 y2\<close> \<open>x1 \<noteq> x2\<close>)
    then show ?thesis 
    proof (cases m)
      case (A2Horizontal y3)
      have "(y3 = -y1)" using  assms(4) A2meets.cases pf
        by (simp add: A2Horizontal)  
      then show ?thesis using u1 A2Horizontal by auto 
    next
      case (A2Ordinary x3 y3)
      have 0: "x1 + x3*y1 + y3 = 0" using assms(4) A2meets.cases pf A2Ordinary by auto
      have 1: "x2 + x3*y2 + y3 = 0" using assms(5) A2meets.cases qf A2Ordinary by auto
      have 2: "x1 - x2 + x3*(y1 -y2) = 0" using 0 1 by algebra
      have 4: "x1 - x2 = 0" using 2 True by algebra
      have "False" using 4 e by algebra
      then show "\<And>x11 x12. A2join P Q = A2Horizontal (- y1) \<Longrightarrow> m = A2Ordinary x11 x12 \<Longrightarrow> m = A2join P Q" by auto
    qed
  next
    case False (* y1 <> y2 *)
    have u1: "A2join P Q = A2Ordinary  ((x2-x1)/(y1-y2)) ((x1*y2-x2*y1)/(y1-y2))" using pf qf A2join.simps
      using False by auto
    then show ?thesis
    proof (cases m)
      prefer 2
      case (A2Horizontal y3)
      have 0:"(y3 = -y1)" using  assms(4) A2meets.cases pf
        by (simp add: A2Horizontal)  
      have 1:"(y3 = -y2)" using  assms(5) A2meets.cases qf
        by (simp add: A2Horizontal)  
      have 2: "y2 = y1" using 0 1 by auto
      have 3: "y2 \<noteq> y1" using False by auto
      then show ?thesis using 2 by auto
    next
      case (A2Ordinary B C)
      have 0: "x1 + B*y1 + C = 0" using assms(4) A2meets.cases pf A2Ordinary by auto
      have 1: "x2 + B*y2 + C = 0" using assms(5) A2meets.cases qf A2Ordinary by auto
      have 2: "(x1 - x2) + B*(y1-y2) = 0" using 0 1 by algebra
      have 3: "B = (x2 - x1)/(y1 - y2)" using 2 False   by (simp add: eq_divide_eq) 
      have 4: "x1 +  ((x2 - x1)/(y1 - y2))*y1 + C = 0" using 0 3 by algebra
      have 5: "( x1* y2 -  x2*y1 )/(y1 - y2) = C"  using "4" pf u1 u2 by force
      have 6: "m = A2Ordinary ((x2 - x1)/(y1 - y2)) (( x1* y2 -  x2*y1 )/(y1 - y2))" using 3 5 A2Ordinary by blast
      then show ?thesis using u1 by auto
    qed

  qed
qed

theorem  A2a2a: 
  assumes "P \<in> A2Points" and "l \<in> A2Lines"
  shows  "A2find_parallel l P \<in> A2Lines"
  by (simp add: A2Lines_def) 

theorem  A2a2b:
  assumes "P \<in> A2Points" and "l \<in> A2Lines"
  shows  "affine_plane_data.parallel A2Points A2Lines A2meets (A2find_parallel l P) l"
proof -
  obtain x1 y1 where  pf: "P  = A2Point x1 y1"
    using a2pt.exhaust by blast 

  have "?thesis =
  (if ((A2find_parallel l P) \<in> A2Lines \<and> l \<in> A2Lines) 
  then (A2find_parallel l P) = l \<or> \<not> (\<exists> Pa. Pa \<in> A2Points \<and> A2meets Pa (A2find_parallel l P) \<and> A2meets Pa l) else undefined)"
    unfolding affine_plane_data.parallel_def using assms by auto
  also have "... = ((A2find_parallel l P) = l \<or> 
    \<not> (\<exists> Pa. Pa \<in> A2Points \<and> A2meets Pa (A2find_parallel l P) \<and> A2meets Pa l))" 
    using assms A2a2a by auto
  presume p: " ((A2find_parallel l P) = l \<or> 
    \<not> (\<exists> Pa. Pa \<in> A2Points \<and> A2meets Pa (A2find_parallel l P) \<and> A2meets Pa l))"
  show ?thesis 
    using p A2Lines_def calculation by auto 
next
  show "A2find_parallel l P = l \<or>
    (\<nexists>Pa. Pa \<in> A2Points \<and> A2meets Pa (A2find_parallel l P) \<and> A2meets Pa l)" 
  proof (cases "A2find_parallel l P =l")
    case True
    then show ?thesis by auto
  next
    case False
    have np: "A2find_parallel l P \<noteq> l" using False by auto
    presume p: "(\<nexists>Pa. Pa \<in> A2Points \<and>  
          A2meets Pa (A2find_parallel l P) \<and>
          A2meets Pa l)"
    then show ?thesis using False by auto
    show u:"\<nexists>Pa. Pa \<in> A2Points \<and>
         A2meets Pa
          (A2find_parallel l P) \<and>
         A2meets Pa l" 
    proof (rule ccontr)  (* np: find_parallel l P \<noteq> l; need to show there's no point Pa on both l and find_parallel l p *)
                     (* P = (x1, x2) by pFact *)
      assume h:"\<not> (\<nexists>Pa. Pa \<in> A2Points \<and> A2meets Pa (A2find_parallel l P) \<and> A2meets Pa l)"
      have h2: "\<exists> Pa . Pa \<in> A2Points \<and> A2meets Pa (A2find_parallel l P) \<and> A2meets Pa l" using h by blast
      obtain x2 y2 where  paf: "Pa  = A2Point x2 y2"
          using h p by blast
      have r: "A2meets Pa l" using h2 p by blast
      show False
      proof (cases l)
        case (A2Ordinary B C)
        have 3: "A2find_parallel l P =  A2Ordinary B (-x2 - B * y2)" 
          using h p by blast
        have pal: "A2meets Pa l" using h2 paf
          using p by blast 
        have 1: "x2 + B* y2 + C = 0" using pal using h p by blast
        have 2: "C = -x2 - B * y2" using 1 by (simp add:algebra_simps)
        have "l = A2Ordinary B ( -x2 - B * y2)" using 2 A2Ordinary by auto
        have 4: "l = A2find_parallel l P" using 3
          using "2" A2Ordinary by auto
        have False using np 4 by auto
        thus ?thesis by auto
      next
        case (A2Horizontal C)
        have yf1: "C = -y2" using hMeets paf r A2Horizontal by blast
        have yf2: "C = -y1" using hMeets using h p by blast
        have "y1 = y2" using yf1 yf2 by auto
        have zf: "A2find_parallel l P =l" using A2Horizontal
          using h p by blast
        have False using zf np by auto
        then show ?thesis by auto
      qed
    qed
    show v:"A2find_parallel l P \<noteq> l \<Longrightarrow>
    \<nexists>Pa. Pa \<in> A2Points \<and>
         A2meets Pa
          (A2find_parallel l P) \<and>
         A2meets Pa l"
      using u by blast 
  next
    show "A2find_parallel l P \<noteq> l \<Longrightarrow>
    \<nexists>Pa. Pa \<in> A2Points \<and>
         A2meets Pa
          (A2find_parallel l P) \<and>
         A2meets Pa l"
      by (smt (verit) A2find_parallel.simps(1) A2find_parallel.simps(2) A2meets.simps(1) A2meets.simps(2) a2ln.exhaust a2pt.exhaust) 
  qed
qed


theorem  A2a2c1:
  assumes "P \<in> A2Points" and "l \<in> A2Lines"
  assumes "l = A2Horizontal C"
  shows  "A2meets P (A2find_parallel l P)"
proof -
  obtain x1 y1 where  pf: "P  = A2Point x1 y1" using assms
    using a2pt.exhaust by blast 
  have "A2find_parallel l P = A2Horizontal (-y1)" using A2find_parallel.simps assms pf by blast
  thus "A2meets P (A2find_parallel l P)" using A2meets.simps assms pf by auto 
qed

theorem  A2a2c2:
  assumes "P \<in> A2Points" and "l \<in> A2Lines"
  assumes "l = A2Ordinary B C"
  shows  "A2meets P (A2find_parallel l P)"
proof -
  obtain x1 y1 where  pf: "P  = A2Point x1 y1" using assms
    using a2pt.exhaust by blast 
  have "A2find_parallel l P = A2Ordinary B (-x1 - B * y1)" using A2find_parallel.simps assms pf by blast
  thus "A2meets P (A2find_parallel l P)" using A2meets.simps assms pf by auto 
qed

theorem  A2a2c:
  assumes "P \<in> A2Points" and "l \<in> A2Lines"
  shows  "A2meets P (A2find_parallel l P)"
  using A2a2c1 A2a2c2 assms
  by (meson a2ln.exhaust) 

theorem A2a3prep:
  assumes "P = A2Point 0 0"
  assumes "Q = A2Point 1 0"
  assumes "R = A2Point 0 1"
  shows " \<not> (affine_plane_data.collinear A2Points A2Lines A2meets P Q R)"
proof (rule ccontr)
  assume f0: "\<not> \<not> affine_plane_data.collinear A2Points A2Lines A2meets P Q R"
  have f1:  "affine_plane_data.collinear A2Points A2Lines A2meets P Q R" using f0 by blast
  have f2: "?this = ((if P \<in> A2Points \<and> Q \<in> A2Points \<and> R \<in> A2Points 
  then (\<exists> l. l \<in> A2Lines \<and> A2meets P l \<and> A2meets Q l \<and> A2meets R l) else undefined))" 
   using assms affine_plane_data.collinear.elims
   by (smt (verit))
  also have f3: "... =  (\<exists> l. l \<in> A2Lines \<and> A2meets P l \<and> A2meets Q l \<and> A2meets R l)" 
    using assms A2Points_def by auto 
  have k1: "(\<exists> l. l \<in> A2Lines \<and> A2meets P l \<and> A2meets Q l \<and> A2meets R l)" 
    using f1 f2 f3 calculation by blast
  obtain l where k2: "l \<in> A2Lines \<and> A2meets P l \<and> A2meets Q l \<and> A2meets R l" using k1 by auto
  have k3:"A2meets P l" and k4:"A2meets Q l" using k2 by auto
  have k5: "l = A2join P Q" using k3 k4 A2a1b [where P = P and Q = Q] assms A2Points_def by auto
  have k6: "A2join P Q = A2Horizontal 0" using A2join.simps
    using assms(1) assms(2) by auto
  have k7: "l =  A2Horizontal 0" using k5 k6 by auto
  have k8: "\<not> (A2meets R l)" using k7 assms(3) A2meets.simps by auto
  have k9: "A2meets R l" using k2 by auto
  have k10:False using k8 k9 by auto
  thus "False" using k10 by auto
qed

theorem A2a3: 
  shows "\<exists>P Q R. P \<in> A2Points \<and> Q \<in> A2Points \<and> R \<in> A2Points \<and> P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> 
  \<not> (affine_plane_data.collinear A2Points A2Lines A2meets P Q R)"
proof -
  show ?thesis using A2a3prep [where P = P and Q = Q and R = R]
    by (smt (verit) A2Points_def A2a3prep UNIV_I a2pt.inject) 
qed

theorem A2affine_plane: 
  shows "affine_plane A2Points A2Lines A2meets A2join A2find_parallel"
proof -
  show ?thesis using A2a1a A2a1b A2a2a A2a2b A2a2c A2a3 by (simp add:affine_plane_def)
qed


end
