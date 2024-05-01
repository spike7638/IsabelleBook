theory AffineExample
  imports Complex_Main 
    begin

datatype a4pt = Pa | Qa | Ra | Sa
definition  "A4Points = {Pa, Qa, Ra, Sa}"
definition "A4PQ = {Pa, Qa}"
definition "A4PR = {Pa, Ra}"
definition "A4PS = {Pa, Sa}"
definition "A4QR = {Qa, Ra}"
definition "A4QS = {Qa, Sa}"
definition "A4RS = {Ra, Sa}"

definition "A4Lines = {A4PQ, A4PR, A4PS, A4QR, A4QS, A4RS}"

fun parallel::"a4pt set \<Rightarrow> a4pt set \<Rightarrow> bool" where
"parallel l m  =  (if (l \<in> A4Lines \<and> m \<in> A4Lines) 
  then l = m \<or> (l \<inter> m = {}) else undefined)"

fun A4complement::"a4pt set \<Rightarrow> a4pt set" where
"A4complement n = (if n \<in> A4Lines then A4Points-n else undefined)"

(*
"A4complement n = (if n = A4PQ then A4RS else 
(if n = A4RS then A4PQ else 
(if n = A4PR then A4QS else
(if n = A4QS then A4PR else 
(if n = A4PS then A4QR else 
(if n = A4QR then A4PS else 
undefined))))))"
*)

lemma complement_disjoint:
  fixes X::"'a set" 
  fixes A::"'a set" 
  shows "(X - A) \<inter> A = {}"
  by blast


lemma complement_different:
  fixes A::"a4pt set" 
  shows "(A4Points - A) \<noteq> A"
  using A4Points_def by blast

lemma A4complement_parallel: 
  fixes n
  assumes "n \<in> A4Lines"
  shows "parallel (A4complement n) n"
proof -
  have 1: "A4complement n = A4Points - n" using  A4complement.simps assms by auto

  have 11: "parallel (A4complement n) n = parallel A4PQ A4RS" using 0 1  by auto
  
  have 2: "parallel A4PQ A4RS = (if (A4PQ \<in> A4Lines \<and> A4RS \<in> A4Lines)
  then A4PQ = A4RS \<or> (A4PQ \<inter>  A4RS = {}) else undefined) " using parallel.simps by auto

  have 3: "parallel A4PQ A4RS = (if (True \<and> True)
  then A4PQ = A4RS \<or> (A4PQ \<inter>  A4RS = {}) else undefined) " using A4Lines_def  by auto

  have 4: "parallel A4PQ A4RS = (if (True \<and> True)
  then False \<or> (A4PQ \<inter>  A4RS = {}) else undefined) " using 3 A4PQ_def A4RS_def by auto

  have 5: "parallel A4PQ A4RS = (if True
  then  (A4PQ \<inter>  A4RS = {}) else undefined) " using 4  by auto

  have 6: "parallel A4PQ A4RS =  (A4PQ \<inter>  A4RS = {})" using 5  by auto
  have 7: "parallel A4PQ A4RS =  True" using 6 A4PQ_def A4RS_def
    by (metis Diff_disjoint Diff_insert_absorb Int_insert_left_if0 a4pt.distinct(3) a4pt.distinct(5) a4pt.distinct(7) a4pt.distinct(9) insert_absorb insert_iff singleton_insert_inj_eq')


  have 8: "parallel A4PQ A4RS" using 7 by auto
  show  "parallel (A4complement n) n" using 1 11 2 3 4 5 6 7 8 by auto
 
qed
(* I'd like to say "let's consider each possible value of n, namely A4PQ, A4PR, A4PS, etc" and show the conclusion 
for each of these, i.e., do a "cases" on the enumerated values in the set A4Lines. I cannot figure out how to do this, so this failed attempt
goes in the dustbin as an example of getting oneself wedged *)

end