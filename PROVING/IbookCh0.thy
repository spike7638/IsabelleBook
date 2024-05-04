theory IbookCh0
  imports Main
begin

lemma "evens": "\<exists> (n::nat) . 2*n > (k::nat)"
  by presburger

lemma "evens2": "\<exists> (n::nat) . 2*n > (k::nat)"
  using evens by auto

lemma "evens3": "\<exists> (n::nat) . 2*n > (k::nat)"
proof -
  have example:"2*(k+1) > k" 
    by simp
  show ?thesis 
    using example by blast
qed

lemma "evens4": "\<exists> (n::nat) . 2*n > (k::nat)"
proof (cases "k = 0") (* Split into cases where this is True or False *)
  case True           (* "True" becomes a synonym for "k = 0" *)
  have ex: " 2 * 1 > k" using True by simp  (* and we use it! *)
  then show ?thesis using ex by blast
next
  case False (* "False" is a synonym for k \<noteq> 0 *)
  have ex: "2 * k > k" using False by auto (* we use it here *)
  then show ?thesis using ex by blast (* and now there are no goals left *)
qed

(* For this proof, we use the idea that every natural number is either zero, 
 * or the "successor" of some natural number, i.e., an inductive construction 
 * of the naturals. "Suc" is the successor-function built into Isabelle's Main theory.
 *)

lemma "evens5": " \<exists> (n::nat) . 2*n > (k::nat)"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then obtain n where nFact: "2*n > k" by blast
  let ?m = "Suc n" 
  from nFact have "2 * ?m > Suc k" by auto
  then show ?case by blast
qed

(* Fleury's proof *)
lemma "T5": " \<exists> (n::nat) . (k::nat) + 5 < n"
proof (induction k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  then obtain n where n: \<open>k + 5 < n\<close> \<comment>\<open>From this, I'd like to say "OK, so there's some n with that property. Let's call it m.\<close>
    by blast
  let ?p = \<open>Suc n\<close>
  from n have \<open>Suc k + 5 < ?p\<close> \<comment>\<open>I show that Suc k + 5 < p for some p (as I did in the k = 0 case)\<close>
    by auto
  then show ?case try0
    by (rule exI[of _ \<open>Suc n\<close>]) \<comment>\<open>Isabelle can infer the "there-exists" result from that instance, using P(a) => EX x . P(x). \<close>
qed

(* Example of apply-script proof *)

definition nand :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infixr "N" 35)
  where "A N B \<equiv> \<not>(A \<and> B)"

lemma " \<not>A \<longleftrightarrow> A N A"
  unfolding nand_def
  apply simp
  done

(* ==== END OF EXAMPLE ==== *)
(* poss'll add'l problem: "Take two numbers; add them and
subtract them; then take the difference of those two results.
Your answer will be twice the smaller number. Amazing!" 
Restate in fix-assume-show format.
*)

(* Homework problems *)
lemma "odds1": " \<exists> (k::nat) . 2*k+1 > (n::nat)"
proof -
  have "2*n+1 > n" by auto
  thus ?thesis by blast
qed

lemma "positiveSquare": "(n::nat) * (n::nat) \<ge> 0"
  by auto

(* 
lemma "positivePolynomial": "(n::nat) * n - n + 1 > 0"
proof (cases "n=0")
  case True
  then show ?thesis by auto
next
  case False
  then  
    have 0:"  n  = 2*n  - n" by simp
    also have 1: "(k::nat) = k" by auto
    have 2:"k-n = k - (2*n - n)" using 0 1 by simp
    have "((n-1)*(n-1))
qed

*)

end
