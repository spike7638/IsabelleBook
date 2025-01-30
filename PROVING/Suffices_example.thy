theory Suffices_example
  imports Main Complex_Main
begin
   (* Prove that x^2 + xy + y^2 \<ge> 0 for x,y in R *)
(* One approach: rewrite it as (x + y/2)^2 + (3/4)y^2, which is evidently nonnegative.
We could write a lemma that u^2 \<ge> 0, apply it to two different things, sum them, and get the result. 
Let's do that *)

lemma squareNN:
  fixes x::real
  shows "x^2 \<ge> 0"
proof -
  show ?thesis by simp
qed

lemma twoSquares:
  fixes x::real and y::real
  shows "0 \<le> x^2 + y^2"
proof-
  show ?thesis using squareNN by simp
qed

(*
lemma 
  fixes x::real and y::real
  shows "x^2 + x*y + y^2 \<ge> 0"
proof -
  have 1: "4*x^2 +4* x*y + 4*y^2 = (4*x^2 + 4*x*y + (y^2)) + 3*y^2" by simp
  have 2: "(4*x^2 + 4*x*y + y^2) = (2*x + y)^2" by (simp add: power2_sum) 
  have 3: "4*x^2 +4* x*y + 4*y^2 = (2*x + y)^2 + 3*y^2" using 1 2 by simp
  have 4: "0 \<le> (2*x + y)^2 + 3*y^2" using 3 twoSquares [of "(2*x +y)" "y" ] by simp
  have 5: "0 \<le> 4*x^2 +4* x*y + 4*y^2" using 3 4 by presburger
  show ?thesis using 5 by auto
end
*)

lemma 
  fixes x::real and y::real
  shows "x^2 + x*y + y^2 \<ge> 0"
proof -
  presume A: "0 \<le> 4*x^2 + 4*x*y + 4*y^2"
  show ?thesis using A by auto
next
  show "0 \<le> 4*x^2 + 4*x*y + 4*y^2"  
  proof -
    have 1: "4*x^2 +4* x*y + 4*y^2 = (4*x^2 + 4*x*y + (y^2)) + 3*y^2" by simp
    have 2: "(4*x^2 + 4*x*y + y^2) = (2*x + y)^2" by (simp add: power2_sum) 
    have 3: "4*x^2 +4* x*y + 4*y^2 = (2*x + y)^2 + 3*y^2" using 1 2 by simp
    have 4: "0 \<le> (2*x + y)^2 + 3*y^2" using 3 twoSquares [of "(2*x +y)" "y" ] by simp
    thus ?thesis  using 4 3 by presburger
  qed
qed

lemma
  assumes "A" "A \<Longrightarrow> B"
  shows "B"
proof-
  presume Q: "A"
  show ?thesis using Q assms(2) by auto
next
  show "A"
  proof -
    show ?thesis  using assms(1)  by simp
  qed
qed

end