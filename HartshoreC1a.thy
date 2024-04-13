theory Chapter1a
  imports Complex_Main
begin
text \<open>
Contents:
\<^item> We formalize the first chapter of Hartshorne's "Projective Geometry"
\<^item> Propositions like "1.1" in the text are given names like Prop1P1 (with "P" replacing the 
decimal point
\<close>

  text{* We've based our theory on "Complex_Main" instead of main so that we have the datatype "real". *}

  text \<open>
We begin with a "locale" (roughly speaking, a set of assumptions to work with, so that, 
for instance, one might put all the axioms of a group into a "local" and then assert 
that various things we construct constitute a "group". The locale-name becomes a predicate,
so we could say something like "group integers (+) (*)" to mean that the (previously constructed) 
set of integers, together with addition and multiplication constitutes a group. Our first locale 
prescribes the data needed to describe an affine plane, and a few definitions that come up 
in the axioms for an affine plane. 
\<close>
text \<open>
Here we are saying that to have an affine plane, you need two types (which are how we represent
sets in Isabelle), and a relationship between them. The statement "meets P l" indicates the notion
that the "point" P lies on the "line" l. For Hartshorne, we would say P is an element of l, but using
point sets as lines turns out to be a horrible idea in Isabelle, so we just deal with "meets". 
\<close>

  locale affine_plane_data =
    fixes meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool"

  begin

    definition parallel:: "'line  \<Rightarrow> 'line \<Rightarrow> bool" (infix "||" 50)
      where "l || m \<longleftrightarrow> (l = m \<or> \<not> (\<exists> P. meets P l  \<and> meets P m))"

    definition collinear :: "'point  \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool"
      where "collinear A B C \<longleftrightarrow> (\<exists> l. meets A l \<and> meets B l \<and> meets C l)"
  end

  locale affine_plane =
    affine_plane_data meets
  for meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool" +
  assumes
    a1: "P \<noteq> Q \<Longrightarrow> \<exists>!l. meets P l \<and> meets Q l" and
    a2: "\<not> meets P l \<Longrightarrow> \<exists>!m. l || m \<and> meets P m" and
    a3: "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R"

begin

  lemma symmetric_parallel: "l || m \<Longrightarrow> m || l"
    using parallel_def by auto

  lemma reflexive_parallel: "l || l"
    by (simp add: parallel_def)

  lemma transitive_parallel: "\<lbrakk>l || m ;  m || n\<rbrakk> \<Longrightarrow> l || n"
    by (metis a2 parallel_def)
  section {* The real affine plane *}
  text{* Hartshorne mentions the ordinary affine plane as an example of a plane. We should prove 
that it's actually an affine plane. It's pretty clear how to represent points --- pairs of real 
numbers --- but what about lines? A line is the set of points satisfying an equation of 
the form Ax + By + C = 0, with not both of A and B being zero. The problem is that there's 
no datatype for "pair of real numbers, at least one of which is nonzero". We'll have 
to hack this by breaking lines into "ordinary" and "vertical", alas. The proofs of
the three axioms are appallingly long, and you should absolutely skip them on a first reading.   *}

  datatype a2pt = A2Point "real" "real"

  datatype a2ln = A2Ordinary "real" "real" 
                | A2Vertical "real"
  text "Ordinary m b represents the line y = mx+b; Vertical x0 is the line x = x0 "

  fun a2meets :: "a2pt \<Rightarrow> a2ln \<Rightarrow> bool" where
    "a2meets (A2Point x y) (A2Ordinary m b) = (y = m*x + b)" |
    "a2meets (A2Point x y) (A2Vertical xi) = (x = xi)"

 lemma A2_a1: "P \<noteq> Q \<Longrightarrow> \<exists>! l . a2meets P l \<and> a2meets Q l"
  proof -
    assume P_ne_Q: "P \<noteq> Q"
    show "\<exists>! l . a2meets P l \<and> a2meets Q l"
    proof (cases P, cases Q)
      fix px py qx qy
      assume P: "P = A2Point px py"
      assume Q: "Q = A2Point qx qy"
      show "\<exists>! l . a2meets P l \<and> a2meets Q l"
      proof (cases "px = qx")
        assume eq: "px = qx"
        show "\<exists>!l. a2meets P l \<and> a2meets Q l"
        proof
          show "a2meets P (A2Vertical px) \<and> a2meets Q (A2Vertical px)"
            using P Q eq by simp
          show "\<And>l. a2meets P l \<and> a2meets Q l \<Longrightarrow> l = A2Vertical px"
          proof -
            fix l
            show "a2meets P l \<and> a2meets Q l \<Longrightarrow> l = A2Vertical px"
            proof (cases l)
              show "\<And>m b. a2meets P l \<and> a2meets Q l \<Longrightarrow> l = A2Ordinary m b \<Longrightarrow> l = A2Vertical px"
                using P Q P_ne_Q eq by simp
              show "\<And>x. a2meets P l \<and> a2meets Q l \<Longrightarrow> l = A2Vertical x \<Longrightarrow> l = A2Vertical px"
                using P by simp
            qed
          qed
        qed
        next
        assume neq: "px \<noteq> qx"
        show "\<exists>!l. a2meets P l \<and> a2meets Q l"
        proof
          let ?m = "(qy - py)/(qx - px)"
          let ?b = "py - ?m * px"
          have *: "py = ?m * px + ?b \<and> qy = ?m * qx + ?b"
          proof -
            have "?m * qx - ?m * px + py = ?m * (qx - px) + py"
              by argo
            also have "... = qy - py + py"
              using neq by simp
            also have "... = qy"
              by simp
            finally show ?thesis by simp
          qed
          show "a2meets P (A2Ordinary ?m ?b) \<and> a2meets Q (A2Ordinary ?m ?b)"
            using * P Q by simp
          show "\<And>l. a2meets P l \<and> a2meets Q l \<Longrightarrow> l = A2Ordinary ?m (py - ?m * px)"
          proof -
            fix l
            assume l: "a2meets P l \<and> a2meets Q l"
            show "l = A2Ordinary ?m (py - ?m * px)"
            proof (cases l)
              case (A2Ordinary m b)
              assume 1: "l = A2Ordinary m b"
              have "py = m * px + b \<and> qy = m * qx + b"
                using P Q l 1 by simp
              hence "m = ?m \<and> b = ?b"
                using neq by (smt "*" crossproduct_noteq)  (* Found with sledgehammer *)
              thus "l = A2Ordinary ?m ?b"
                using 1 by simp
            next
              case (A2Vertical x)
              assume 1: "l = A2Vertical x"
              then show "l = A2Ordinary ?m ?b"
                using 1 P Q l neq by simp
            qed
          qed
        qed
      qed
    qed
  qed

(* Lemma: if P lies on l and k, and l is parallel to k, then l = k *)
lemma A2_a2unique: "a2meets P l \<and> a2meets P k \<and> ((l = k)\<or> \<not> (\<exists> T. a2meets T l  \<and> a2meets T k))   \<Longrightarrow> l = k"
proof -
  show "a2meets P l \<and> a2meets P k \<and> ((l = k)\<or> \<not> (\<exists> T. a2meets T l  \<and> a2meets T k))   \<Longrightarrow> l = k"
    by auto
qed

(* Here are several proofs, simpler and simpler, of the following lemma; the first one is a failed
proof, however *)
(* Lemma: vertical lines with different x-coords are disjoint *)
(*lemma A2_vert1: "x0 \<noteq> x1 \<and> l = A2Vertical x0 \<and> k = A2Vertical x1   \<Longrightarrow>  \<not> (\<exists> T. a2meets T l  \<and> a2meets T k)"
proof -
  assume diff_x: "x0 \<noteq> x1"
  assume l_form: "l = A2Vertical x0"
  assume k_form: "k = A2Vertical x1"

  have "\<not> (\<exists> T. a2meets T l  \<and> a2meets T k)"
  proof (rule ccontr)
    assume a1: "\<not>\<not> (\<exists> T. a2meets T l  \<and> a2meets T k)"
    have a1p: "(\<exists> T. a2meets T l  \<and> a2meets T k)"
      using a1 by blast
    fix u v
    assume T_form: "T = A2Point u v"
    have T_on_l: "a2meets T l"
      by (metis \<open>\<exists>T. a2meets T l \<and> a2meets T k\<close> a2meets.elims(2) a2meets.simps(2) diff_x k_form l_form)
    have T_on_k: "a2meets T k" 
      by (metis \<open>\<exists>T. a2meets T l \<and> a2meets T k\<close> a2meets.elims(2) a2meets.simps(2) diff_x k_form l_form)
    have "u = x0" 
      using T_form T_on_l l_form by auto
    have "u = x1" 
      using T_form T_on_k k_form by auto
    have False sorry 
  qed
  sorry
  sorry
*)
(*      using \<open>u = x0\<close> \<open>u = x1\<close> diff_x by blast
    sorry
qed 
  sorry *)
(* A direct proof, rather than contradiction *)
(* Lemma: vertical lines with different x-coords are disjoint *)
(*
lemma A2_vert2: "x0 \<noteq> x1 \<and> l = A2Vertical x0 \<and> k = A2Vertical x1   \<Longrightarrow>  \<not> (\<exists> T. a2meets T l  \<and> a2meets T k)"
proof -
 assume diff_x: "x0 \<noteq> x1"
 assume l_form: "l = A2Vertical x0"
 assume k_form: "k = A2Vertical x1"
 have "\<not> (\<exists> T. a2meets T l  \<and> a2meets T k)"
 proof
   assume "\<exists> T. a2meets T l  \<and> a2meets T k"
   then obtain T where T_on_l: \<open>a2meets T l\<close> and T_on_k: \<open>a2meets T k\<close>
     by blast
   obtain u v where T_form: "T = A2Point u v"
     by (cases T)
   have "u = x0"
     using T_form T_on_l l_form by auto
   have "u = x1"
     using T_form T_on_k k_form by auto
   show False
     using \<open>u = x0\<close> \<open>u = x1\<close> diff_x by blast
 qed
  thus ?thesis
*)
  




(* A slightly shorter version-- the assumptions are gathered under "assumes" rather than using
multiple "assume" clauses, and these assumes-and-shows things ARE the statement of the theorem! The proof
remains identical *)

lemma A2_vert3:
  assumes
    diff_x: \<open>x0 \<noteq> x1\<close> and
    l_form: \<open>l = A2Vertical x0\<close> and 
    k_form: \<open>k = A2Vertical x1\<close>
  shows \<open>\<not> (\<exists>T. a2meets T l  \<and> a2meets T k)\<close>
proof
  assume "\<exists> T. a2meets T l  \<and> a2meets T k"
  then obtain T where T_on_l: \<open>a2meets T l\<close> and T_on_k: \<open>a2meets T k\<close>
    by blast
  obtain u v where T_form: "T = A2Point u v"
    by (cases T)
  have "u = x0"
    using T_form T_on_l l_form by auto
  have "u = x1"
    using T_form T_on_k k_form by auto
  show False
    using \<open>u = x0\<close> \<open>u = x1\<close> diff_x by blast
qed

(* In the commented-out proof above, there's a fundamental problem with :"T", which is that it end
up unbound, but also, mid-proof, there's a note from metis that "Metis: The assumptions are inconsistent",
which really tells us the proof could be MUCH shorter, and metis knows how to make it shorter! *)
lemma A2_vert4:
  assumes
    diff_x: \<open>x0 \<noteq> x1\<close> and
    l_form: \<open>l = A2Vertical x0\<close> and 
    k_form: \<open>k = A2Vertical x1\<close>
  shows \<open>\<not> (\<exists>T. a2meets T l  \<and> a2meets T k)\<close>
  by (metis assms a2meets.elims(2)
      a2meets.simps(2) diff_x k_form l_form)

(* Finally, a version that states and proves the contrapositive, and uses some other syntax ("defines"?)
to simplify things a bit. *)

lemma A2_vert5:
  fixes x0 x1 :: real
  defines l_form: \<open>l \<equiv> A2Vertical x0\<close> 
  defines k_form: \<open>k \<equiv> A2Vertical x1\<close>
  assumes \<open>a2meets T l\<close> and \<open>a2meets T k\<close>
  shows \<open>l = k\<close> 
  by (cases T) (use assms in auto)

text \<open>vertical and ordinary lines always intersect\<close>
lemma A2_vert_ord:
  fixes x0 m b :: real 
  assumes
    l_form: \<open>l = A2Vertical x0\<close> and 
    k_form: \<open>k = A2Ordinary m b\<close> and
    t_form: \<open>T = A2Point x0 (m*x0 + b)\<close>
  shows \<open>\<exists>T. a2meets T l  \<and> a2meets T k\<close> 
  by try 
(*

(metis assms a2meets.elims(2)
      a2meets.simps(2) t_form k_form l_form)




assumes
    l_form: \<open>l = A2Vertical x0\<close> and 
    k_form: \<open>k \<equiv> A2Ordinary m b\<close>
  shows  \<open>\<exists>T . a2meets T l \<and> a2meets T k\<close>
  by try0


  shows "\<exists>T . a2meets T l \<and> a2meets T k"


shows \<open>\<not> (\<exists>T. a2meets T l  \<and> a2meets T k)\<close>

  defines l_form: \<open>l \<equiv> A2Vertical x0\<close> 
  defines k_form: \<open>k \<equiv> A2Ordinary m b\<close>
  by try

*) 

(* (cases T) (use assms in auto) *)

(*   obtains T where \<open>T \<equiv> A2Point x0 (m*x0 + b)\<close>
*)





  (* If P not on L, there's a line k different from l with k || l and P on k *)
  (* Easy corollary: if P not on L, there's a unique line k containing P with k || l *)

lemma A2_a2exist1: "\<not> a2meets P l \<Longrightarrow> \<exists> k. a2meets P k \<and>  \<not> (\<exists> T. a2meets T l  \<and> a2meets T k)"
proof (cases l)
  fix u v
  assume P_form: "P = A2Point u v"
  case (A2Vertical x0)
  assume not_on :"\<not> a2meets P l"
  have "u \<noteq> x0" 
  using A2Vertical P_form not_on by auto
  let ?k = "A2Vertical u"
  show  "\<not> (\<exists> T. a2meets T l  \<and> a2meets T k)"
  using A2_vert5 by auto
  fix u v
  assume P_form: "P = A2Point u v"
  assume P_not_on_l: "\<not> a2meets P l"
  have "u \<noteq> x0" try
    using A2Vertical P_form P_not_on_l by auto
  fix k
  assume k_form:"k = A2Vertical u"
  have "a2meets P k" 
    by (simp add: P_form k_form)
  have "(\<nexists>T. a2meets T l \<and> a2meets T k)"
    using A2Vertical A2_vert4 \<open>u \<noteq> x0\<close> k_form by blast
  done
    using P_form P_not_on_l a2meets.simps(2) l_form by blast
  let ?k = "A2Vertical u"
  have "a2meets P ?k"
    by (simp add: P_form)
  then show ?thesis try
    sorry
next
  case (A2Ordinary x11 x12)
  then show ?thesis sorry
qed

lemma A2_a2a (*existence*): "\<not> a2meets P l \<Longrightarrow>
    \<exists>n. ((l = m)\<or> \<not> (\<exists> T. a2meets T l  \<and> a2meets T n)) \<and> a2meets P n"
    proof -
    assume P_not_on_l: "\<not> a2meets P l"
    show "\<not> a2meets P l \<Longrightarrow> \<exists>n. ((l = n)\<or> \<not> (\<exists> T. a2meets T l  \<and> a2meets T n)) \<and> a2meets P n"

    proof (cases l)
      case (A2Ordinary m b)
      then show ?thesis sorry
    next
      case (A2Vertical x0)
      then show ?thesis sorry
    qed
      fix px py m b
      assume P: "P = A2Point px py"
      assume eq: "l = A2Ordinary m b"
      show  "\<not> a2meets P l \<Longrightarrow>
    \<exists>m. ((l = m)\<or> \<not> (\<exists> T. a2meets T l  \<and> a2meets T m)) \<and> a2meets P m"
      proof -

        show "\<exists>! l . a2meets P l \<and> a2meets Q l"
        show "\<exists>!l. a2meets P l \<and> a2meets Q l"
        proof
          show "a2meets P (A2Vertical px) \<and> a2meets Q (A2Vertical px)"
            using P Q eq by simp
          show "\<And>l. a2meets P l \<and> a2meets Q l \<Longrightarrow> l = A2Vertical px"
          proof -
            fix l
            show "a2meets P l \<and> a2meets Q l \<Longrightarrow> l = A2Vertical px"
            proof (cases l)
              show "\<And>m b. a2meets P l \<and> a2meets Q l \<Longrightarrow> l = A2Ordinary m b \<Longrightarrow> l = A2Vertical px"
                using P Q P_ne_Q eq by simp
              show "\<And>x. a2meets P l \<and> a2meets Q l \<Longrightarrow> l = A2Vertical x \<Longrightarrow> l = A2Vertical px"
                using P by simp
            qed

  lemma A2_a2b(*uniqueness*): 
    "\<lbrakk>\<not> a2meets P l; a2meets P m;  \<not> (\<exists> T. a2meets T l  \<and> a2meets T m); 
      a2meets P n;  \<not> (\<exists> U. a2meets U l  \<and> a2meets U n)\<rbrakk> 
     \<Longrightarrow> m = n"
    sorry

  lemma A2_a3:  "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> (\<nexists> m. a2meets P m \<and> a2meets Q m \<and> a2meets R m)"
    sorry


  section "Basic properties of affine planes, and easy proofs"

  (* Examples of some easy theorems about affine planes, not mentioned in Hartshorne *)
  (* Every point lies on some line *)
  lemma containing_line: " \<forall>S. \<exists>l. meets S l"
    using a2 by blast

  (* Every line contains at least one point *)
  lemma contained_point: "\<forall>l. \<exists>S. meets S l"
    using a1 a2 a3 parallel_def collinear_def by metis

  (* Two lines meet in at most one point *)
  lemma (in affine_plane) prop1P2: "\<lbrakk>l \<noteq> m; meets P l; meets P m; meets Q l; meets Q m\<rbrakk> \<Longrightarrow> P = Q"
    using a1 by auto

(* Some HW Problems to give you practice with Isabelle:
Try to state and prove these:
1. Every line contains at least two points (this is stated for you below, but
with "sorry" as a "proof". 
2. Every line contains at least three points [false!]
*)

  lemma (in affine_plane) contained_points: " \<forall> l.  \<exists> S. \<exists> T.  S\<noteq>T \<and> meets S l\<and> meets T l"
    sorry (* remove this line and fill in a proof! *)
(* N.B.: the existence clause above could be condensed to   \<exists> S T . <more>, i.e., we can combine
   multiple existential quantifiers into one. Do so when you formulate your 3-points-on-a-line
   non-theorem. *)

  text \<open>
 We now try to prove that every affine plane contains at least four points. Sledgehammer 
(a generally-useful approach) doesn't get anywhere with this one. 

Here's Hartshorne's proof, though, so we can use the pieces to construct an Isabelle proof.

i. by A3 there are three distinct non-collinear points; call them P,Q,R. 
ii. By A1, there's a line, which I'll call QR, through Q and R. 
iii. By A2, there's a line l through P, parallel to QR.
iv. Similarly, there's a line PQ containing P and Q. 
v. There's a line m through R, parallel to the line PQ.

CASES: l is parallel to m, or it is not.  

vi. l is not parallel to m, for if it were, then PQ || m || l || QR, hence PQ || QR (by 
the lemmas about |\<rparr> and since both contain Q,  they are identical, but then P,Q,R are collinear,
which is a contradiction. 

vii. So l and m are nonparallel, and they share some point S. 

viii. S lies on m, which is parallel to PQ but not equal to it,
hence disjoint from it (see definition of parallel), so S is not on PQ.

ix.  Hence S != P, S != Q. 

x. Similar (arguing about l), we get  S != R. 

xi. Hence the four points P,Q,R,S are all distinct, and we are done. 
\<close>
  proposition four_points_necessary: "\<exists>(P :: 'point) (Q :: 'point) (R :: 'point) (S :: 'point). 
      P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S"
  proof -
    obtain P Q R where PQR: "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R  \<and> \<not> collinear P Q R"
      using a3 by auto

    (* ii. By A1, there's a line, which I'll call QR, through Q and R. *)
    obtain QR where QR: "meets Q QR \<and> meets R QR"
      using PQR a1 by blast

    (* iii. By A2, there's a line l through P, parallel to QR. *)
    obtain l where l: "meets P l \<and> l || QR"
      using a2 parallel_def by metis

    (* iv. Similarly to ii, there's a line PQ containing P and Q. *)
    obtain PQ where PQ: "meets P PQ \<and> meets Q PQ"
      using PQR a1 by blast

    (* v. and similar to iii, there's a line m through R, parallel to the line PQ. *)

    obtain m where m: "meets R m \<and> m || PQ"
      using a2 parallel_def by metis

    (* CASES: l is parallel to m, or it is not. *)
    (*
          vi. l is not parallel to m, for if it were, then PQ || m || l || QR, hence PQ || QR (by 
          the lemmas about |\<rparr> and since both contain Q,  they are identical, but then P,Q,R are collinear,
          which is a contradiction.
     *)
    (* NB : We have no actually split into cases here, but rather just prove directly that l || m 
        is impossible. *) 
    have "\<not> (l || m)"
    proof
      assume 1: "l || m"
      hence "m || l"
        using 1 symmetric_parallel by simp
      moreover have "PQ || m \<and> l || QR"
        using m l symmetric_parallel by blast
      ultimately have "PQ || QR"
        using transitive_parallel by blast
      hence "PQ = QR \<or> \<not> (\<exists> H. meets H PQ  \<and> meets H QR)"
        by (simp add: parallel_def)
      have "meets Q PQ \<and> meets Q QR"
        by (simp add: PQ QR)
      hence "PQ = QR"
        using \<open>PQ = QR \<or> (\<nexists>H. meets H PQ \<and> meets H QR)\<close> by blast
      hence c1: "collinear P Q R"
        using PQ QR collinear_def by blast
      moreover have  c2: "\<not> (collinear P Q R)"
        using PQR by blast
      thus False
        using PQR calculation by blast
    qed

    obtain S where S: "meets S l \<and> meets S m"
      using \<open>\<not> l || m\<close> parallel_def by blast
    have "\<not> meets S PQ"
      using PQ PQR S affine_plane_data.collinear_def m parallel_def by fastforce
    hence "S \<noteq> P \<and> S \<noteq> Q"
      using PQ by blast
    have "\<not> meets S QR"
      by (metis PQR QR S collinear_def parallel_def l)
    hence "S \<noteq> R"
      using QR by auto
    hence "P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S"
      using PQR \<open>S \<noteq> P \<and> S \<noteq> Q\<close> by blast
    hence "\<exists>(P :: 'point) (Q :: 'point) (R :: 'point) (S :: 'point). P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> P \<noteq> S \<and> Q \<noteq> S \<and> R \<noteq> S"
      by auto
    thus ?thesis by blast
  qed

(* We've now proved the first assertion in the Example after Prop 1.2; we must also show there
IS an affine plane with four points. We'll do this two ways: by explicit construction, and
by using the wonderful "nitpick" 'prover'. *)

(* We start by defining two datatypes, each of which is just an enumerated type; there
are four points and six suggestively-named lines: *)
  datatype pts = Ppt | Qpt | Rpt | Spt
  datatype lns = PQln | PRln | PSln | QRln | QSln | RSln

(* Note: the above datatypes are meant to indicate that "pts" consists of four constructors, 
one for each of P,Q,R and S, and that the line we'd call "PQ" in math is here constructed with
PQln, and we'll define the point-to-line meeting function (i.e., "the point is on the line" so that 
P and Q are on PQln, but R and S are not, etc. *)

(* For the "meets" definition, the syntax looks OCaml-like *)
(* We start by saying which points ARE on the various lines, and then follow with those that 
are not. *)
  fun plmeets :: "pts \<Rightarrow> lns \<Rightarrow> bool" where
    "plmeets Ppt PQln = True" |
    "plmeets Qpt PQln = True" |
    "plmeets Ppt PRln = True" |
    "plmeets Rpt PRln = True" |
    "plmeets Ppt PSln = True" |
    "plmeets Spt PSln = True" | 
    "plmeets Qpt QRln = True" |
    "plmeets Rpt QRln = True" |
    "plmeets Qpt QSln = True" |
    "plmeets Spt QSln = True" |
    "plmeets Rpt RSln = True" |
    "plmeets Spt RSln = True" |

    "plmeets Rpt PQln = False" |
    "plmeets Spt PQln = False" |
    "plmeets Qpt PRln = False" |
    "plmeets Spt PRln = False" |
    "plmeets Qpt PSln = False" |
    "plmeets Rpt PSln = False" |
    "plmeets Ppt QRln = False" |
    "plmeets Spt QRln = False" |
    "plmeets Ppt QSln = False" |
    "plmeets Rpt QSln = False" |
    "plmeets Ppt RSln = False" |
    "plmeets Qpt RSln = False"

  (* Now we'll assert that "plmeets" has all the properties needed to be an affine plane. *)
  lemma four_points_a1: "P \<noteq> Q \<Longrightarrow> \<exists>! l . plmeets P l \<and> plmeets Q l"
    by (smt plmeets.elims(2) plmeets.simps(1) plmeets.simps(10) plmeets.simps(11) plmeets.simps(12) plmeets.simps(13) plmeets.simps(14) plmeets.simps(17) plmeets.simps(18) plmeets.simps(19) plmeets.simps(2) plmeets.simps(20) plmeets.simps(22) plmeets.simps(23) plmeets.simps(3) plmeets.simps(4) plmeets.simps(5) plmeets.simps(6) plmeets.simps(7) plmeets.simps(8) plmeets.simps(9) pts.exhaust)

  lemma four_points_a2a (*existence*): "\<not> plmeets (P :: pts) (l :: lns) \<Longrightarrow> \<exists>m. ((l = m)\<or> \<not> (\<exists> T. plmeets T l  \<and> plmeets T m)) \<and> plmeets P m"
    by (smt lns.simps(27) lns.simps(5) lns.simps(7) plmeets.elims(2) plmeets.simps(1) plmeets.simps(10) plmeets.simps(11) plmeets.simps(12) plmeets.simps(15) plmeets.simps(16) plmeets.simps(17) plmeets.simps(18) plmeets.simps(2) plmeets.simps(22) plmeets.simps(3) plmeets.simps(4) plmeets.simps(5) plmeets.simps(6) plmeets.simps(7) plmeets.simps(8) plmeets.simps(9) pts.exhaust)

(*Exercise: change the first "\<or>" in the lemma above to "\<and>"; that makes the lemma no longer true.
Attempt to prove it with "try" and then make sense of what the output is saying.  *)

  lemma four_points_a2b(*uniqueness*): 
    "\<lbrakk>\<not> plmeets (P :: pts) (l :: lns); plmeets P m;  \<not> (\<exists> T. plmeets T l  \<and> plmeets T m); 
      plmeets P n;  \<not> (\<exists> U. plmeets U l  \<and> plmeets U n)\<rbrakk> 
     \<Longrightarrow> m = n"
    by (smt plmeets.elims(3) plmeets.simps(1) plmeets.simps(11) plmeets.simps(2) plmeets.simps(3) plmeets.simps(4) plmeets.simps(5) plmeets.simps(7) plmeets.simps(8) plmeets.simps(9) pts.simps(11) pts.simps(5) pts.simps(9))

  lemma four_points_a3:  "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> (\<nexists> m. plmeets P m \<and> plmeets Q m \<and> plmeets R m)"
    using four_points_a1 plmeets.simps(1) plmeets.simps(13) plmeets.simps(2) by blast

  proposition four_points_sufficient: "affine_plane plmeets"
    unfolding affine_plane_def
    apply (intro conjI)
    subgoal using four_points_a1 by simp
    subgoal using four_points_a2a four_points_a2b by  (smt affine_plane_data.parallel_def plmeets.simps(11) plmeets.simps(12) plmeets.simps(24))
    apply (simp add: affine_plane_data.collinear_def)
    using four_points_a3 apply (blast)
    done
 
(*
At the suggestion of Manuel Eberl, there's another possibility for this example: define a new
datatype consisting of unordered pairs of points. The "meets" function then becomes very simple. 
Unfortunately, the construction is a messy one so I'm gonna omit it. *)

(* There's another way to show the existence of a 4-point affine plane: you claim that they 
must have at least 5 points, and let "nitpick" show that you're wrong. I'm going to use some
fancy mumbo-jumbo to write this so I can avoid writing out all the pairwise non-equalities; 
this fanciness is due to Manuel Eberl. *)
  proposition five_points_necessary: "\<exists>A::'point set. finite A \<and> card A = 5"
    by nitpick
  oops
(* Pretty nifty, hunh? It's a pain to try to read the output, but the gist is pretty clear: 4 points,
6 lines, each consisting of two distinct points. *)

  definition (in affine_plane_data) point_pencil :: "'point  \<Rightarrow> 'line set"
    where "point_pencil P = {l . meets P l}"

  definition (in affine_plane_data) line_pencil :: "'line  \<Rightarrow> 'line set"
    where "line_pencil l = {m .  l||m}"

  (* I've skipped the notion of 1-1 correspondence, because Isabelle already has a notion 
  of bijections, I believe. *)

  (* Completion of an affine plane to a projective plane *)
  (* Small problem: we need a data type for the points of the projective plane, which consists of
     all points of the affine plane together with all ideal points (i.e., line pencils), and we 
     need another for the lines of the PP, which consists of all lines of the affine plane (extended 
     by their associated ideal point) and the line at infinity consisting of all ideal points. We'll
     return to this, but first we need axioms for a projective plane. *)
  end

  locale projective_plane_data =
    fixes meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool"

  begin
    definition collinear :: "'point  \<Rightarrow> 'point \<Rightarrow> 'point \<Rightarrow> bool"
      where "collinear A B C \<longleftrightarrow> (\<exists> l. meets A l \<and> meets B l \<and> meets C l)"

    definition concurrent :: "'line  \<Rightarrow> 'line \<Rightarrow> 'line \<Rightarrow> bool"
      where "concurrent l m n \<longleftrightarrow> (\<exists> P. meets P l \<and> meets P m \<and> meets P n)"
 
    definition injective :: "('a  \<Rightarrow> 'b)  \<Rightarrow> bool"
      where "injective f  \<longleftrightarrow> ( \<forall> P Q.  (f(P) = f(Q)) \<longleftrightarrow> (P = Q))" 
  end                   
                        

  locale projective_plane =
    projective_plane_data meets
  for meets :: "'point \<Rightarrow> 'line \<Rightarrow> bool" +
  assumes
    p1: "P \<noteq> Q \<Longrightarrow> \<exists>!l. meets P l \<and> meets Q l" and
    p2: "l \<noteq> m \<Longrightarrow> \<exists>!P. meets P l \<and> meets P m" and
    p3: "\<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> \<not> collinear P Q R" and
    p4: "\<forall> l. \<exists>P Q R. P \<noteq> Q \<and> P \<noteq> R \<and> Q \<noteq> R \<and> meets P l \<and> meets Q l \<and> meets R l"

  datatype ('point, 'line) projPoint = Ordinary 'point | Ideal 'line
  datatype ('point, 'line) projLine = OrdinaryL 'line | Infty 

  fun projectivize :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> (('a, 'b) projPoint \<Rightarrow> ('a, 'b) projLine \<Rightarrow> bool)" where
      "projectivize meets (Ordinary P) (OrdinaryL l) = meets P l" 
    | "projectivize meets (Ideal l) (OrdinaryL m) = affine_plane_data.parallel meets l m"
    | "projectivize meets (Ordinary P) Infty = False"
    | "projectivize meets (Ideal l) Infty = True"

  datatype ppts = Ppt | Qpt | Rpt | Spt | PQinf | PRinf | PSinf
  datatype plns = PQln | PRln | PSln | QRln | QSln | RSln | LAI
  fun pmeets :: "ppts \<Rightarrow> plns \<Rightarrow> bool" where
    "pmeets Ppt PQln = True" |
    "pmeets Qpt PQln = True" |
    "pmeets PQinf PQln = True" |

    "pmeets Ppt PRln = True" |
    "pmeets Rpt PRln = True" |
    "pmeets PRinf PRln = True" |

    "pmeets Ppt PSln = True" |
    "pmeets Spt PSln = True" |
    "pmeets PSinf PSln = True" |

    "pmeets Qpt QRln = True" |
    "pmeets Rpt QRln = True" |
    "pmeets PSinf QRln = True" |

    "pmeets Qpt QSln = True" |
    "pmeets Spt QSln = True" |
    "pmeets PRinf QSln = True" |

    "pmeets Rpt RSln = True" |
    "pmeets Spt RSln = True" |
    "pmeets PQinf RSln = True" |

    "pmeets PQinf LAI = True" |
    "pmeets PRinf LAI = True" |
    "pmeets PSinf LAI = True" |


    "pmeets Rpt PQln = False" |
    "pmeets Spt PQln = False" |
    "pmeets PRinf PQln = False" |
    "pmeets PSinf PQln = False" |

    "pmeets Qpt PRln = False" |
    "pmeets Spt PRln = False" |
    "pmeets PQinf PRln = False" |
    "pmeets PSinf PRln = False" |

    "pmeets Qpt PSln = False" |
    "pmeets Rpt PSln = False" |
    "pmeets PQinf PSln = False" |
    "pmeets PRinf PSln = False" |

    "pmeets Ppt QRln = False" |
    "pmeets Spt QRln = False" |
    "pmeets PQinf QRln = False" |
    "pmeets PRinf QRln = False" |

    "pmeets Ppt QSln = False" |
    "pmeets Rpt QSln = False" |
    "pmeets PQinf QSln = False" |
    "pmeets PSinf QSln = False" |

    "pmeets Ppt RSln = False" |
    "pmeets Qpt RSln = False" |
    "pmeets PRinf RSln = False" |
    "pmeets PSinf RSln = False" |

    "pmeets Ppt LAI = False" |
    "pmeets Qpt LAI = False" |
    "pmeets Rpt LAI = False" |
    "pmeets Spt LAI = False" 

theorem "projective_plane pmeets"
    unfolding projective_plane_def
    apply (intro conjI)
    subgoal by (smt plns.exhaust pmeets.simps(1) pmeets.simps(10) pmeets.simps(11) pmeets.simps(12) pmeets.simps(13) pmeets.simps(14) pmeets.simps(15) pmeets.simps(16) pmeets.simps(17) pmeets.simps(18) pmeets.simps(19) pmeets.simps(2) pmeets.simps(20) pmeets.simps(21) pmeets.simps(22) pmeets.simps(23) pmeets.simps(24) pmeets.simps(25) pmeets.simps(26) pmeets.simps(27) pmeets.simps(28) pmeets.simps(29) pmeets.simps(3) pmeets.simps(30) pmeets.simps(31) pmeets.simps(32) pmeets.simps(33) pmeets.simps(34) pmeets.simps(35) pmeets.simps(36) pmeets.simps(37) pmeets.simps(38) pmeets.simps(39) pmeets.simps(4) pmeets.simps(40) pmeets.simps(41) pmeets.simps(42) pmeets.simps(43) pmeets.simps(44) pmeets.simps(45) pmeets.simps(46) pmeets.simps(47) pmeets.simps(48) pmeets.simps(49) pmeets.simps(5) pmeets.simps(6) pmeets.simps(7) pmeets.simps(8) pmeets.simps(9) ppts.exhaust)
    subgoal by (smt plns.exhaust pmeets.simps(1) pmeets.simps(10) pmeets.simps(11) pmeets.simps(12) pmeets.simps(13) pmeets.simps(14) pmeets.simps(15) pmeets.simps(16) pmeets.simps(17) pmeets.simps(18) pmeets.simps(19) pmeets.simps(2) pmeets.simps(20) pmeets.simps(21) pmeets.simps(22) pmeets.simps(23) pmeets.simps(24) pmeets.simps(25) pmeets.simps(26) pmeets.simps(27) pmeets.simps(28) pmeets.simps(29) pmeets.simps(3) pmeets.simps(30) pmeets.simps(31) pmeets.simps(32) pmeets.simps(33) pmeets.simps(34) pmeets.simps(35) pmeets.simps(36) pmeets.simps(37) pmeets.simps(38) pmeets.simps(39) pmeets.simps(4) pmeets.simps(40) pmeets.simps(41) pmeets.simps(42) pmeets.simps(43) pmeets.simps(44) pmeets.simps(45) pmeets.simps(46) pmeets.simps(47) pmeets.simps(48) pmeets.simps(49) pmeets.simps(5) pmeets.simps(6) pmeets.simps(7) pmeets.simps(8) pmeets.simps(9) ppts.exhaust)
    subgoal by (metis (mono_tags, lifting) \<open>\<forall>P Q. P \<noteq> Q \<longrightarrow> (\<exists>!l. pmeets P l \<and> pmeets Q l)\<close> pmeets.simps(11) pmeets.simps(12) pmeets.simps(35) ppts.distinct(29) projective_plane_data.collinear_def)
    subgoal by (smt plns.exhaust pmeets.simps(1) pmeets.simps(10) pmeets.simps(11) pmeets.simps(12) pmeets.simps(13) pmeets.simps(14) pmeets.simps(15) pmeets.simps(16) pmeets.simps(17) pmeets.simps(18) pmeets.simps(19) pmeets.simps(2) pmeets.simps(20) pmeets.simps(21) pmeets.simps(3) pmeets.simps(4) pmeets.simps(5) pmeets.simps(6) pmeets.simps(7) pmeets.simps(8) pmeets.simps(9) ppts.distinct(1) ppts.distinct(11) ppts.distinct(13) ppts.distinct(15) ppts.distinct(17) ppts.distinct(19) ppts.distinct(21) ppts.distinct(23) ppts.distinct(25) ppts.distinct(27) ppts.distinct(29) ppts.distinct(3) ppts.distinct(31) ppts.distinct(33) ppts.distinct(35) ppts.distinct(37) ppts.distinct(39) ppts.distinct(41) ppts.distinct(5) ppts.distinct(7) ppts.distinct(9))
    done

  value "projectivize plmeets (Ordinary Qpt) (Infty)"

theorem projectivization_p1: "\<lbrakk>P \<noteq> Q; affine_plane meets; pm = projectivize meets\<rbrakk> \<Longrightarrow>  \<exists>l. pm P l \<and> pm Q l"
proof -
  assume "P \<noteq> Q"
  assume "affine_plane meets"
  assume "pm = projectivize meets"
  have "\<exists>l. pm P l \<and> pm Q l"
  proof (cases P)
    case (Ordinary p)
    thus ?thesis
    proof (cases Q)
      case (Ordinary q)
      have "p \<noteq> q" using \<open>P = Ordinary p\<close> \<open>P \<noteq> Q\<close> \<open>Q = Ordinary q\<close> by auto
      obtain lo where lo: "meets p lo \<and> meets q lo"  using affine_plane.a1  using \<open>affine_plane meets\<close> \<open>p \<noteq> q\<close> by fastforce
      have "pm P (OrdinaryL lo)" by (simp add: \<open>P = Ordinary p\<close> \<open>pm = projectivize meets\<close> lo)
      moreover have "pm Q (OrdinaryL lo)"  by (simp add: \<open>Q = Ordinary q\<close> \<open>pm = projectivize meets\<close> lo)
      obtain l where l:"pm P l \<and> pm Q l" using \<open>pm Q (OrdinaryL lo)\<close> calculation by auto
      thus ?thesis by blast
    next
      case (Ideal n)
      obtain lo where lo: "meets p lo \<and> affine_plane_data.parallel meets lo n" 
        by (metis \<open>affine_plane meets\<close> affine_plane.a2 affine_plane.reflexive_parallel affine_plane.symmetric_parallel)
      have "pm P (OrdinaryL lo)" 
        by (simp add: Ordinary \<open>pm = projectivize meets\<close> lo) 
      moreover  "pm Q (OrdinaryL lo)" by try 
      thus ?thesis sorry
    thus ?thesis sorry
  next
    case (Ideal l)
    thus ?thesis sorry
   
    assume "P = Ordinary p" and "Q = Ordinary q"
    have "p \<noteq> q" using \<open>P = Ordinary p\<close> \<open>P \<noteq> Q\<close> \<open>Q = Ordinary q\<close> by auto
    obtain lo where lo: "meets p lo \<and> meets q lo"  using affine_plane.a1  using \<open>affine_plane meets\<close> \<open>p \<noteq> q\<close> by fastforce
    have "pm P (OrdinaryL lo)" by (simp add: \<open>P = Ordinary p\<close> \<open>pm = projectivize meets\<close> lo)
    moreover have "pm Q (OrdinaryL lo)"  by (simp add: \<open>Q = Ordinary q\<close> \<open>pm = projectivize meets\<close> lo)
    obtain l where l:"pm P l \<and> pm Q l" using \<open>pm Q (OrdinaryL lo)\<close> calculation by auto
    thus ?thesis 
  next
    assume "P = Ordinary p" and "Q = Ideal l"
    show ?thesis sorry
  next
    assume "P = Ideal l" and "Q = Ordinary q"
    show ?thesis sorry
  next
    assume "P = Ideal l" and "Q = Ideal m"
    show ?thesis sorry
  qed




qed
    have "pm Q (OrdinaryL l)" by apply (simp add: \<open>Q = Ordinary q\<close> \<open>pm = projectivize meets\<close> l)

  note `P = Ordinary p` and `Q = Ordinary q` have "\<exists>l. meets p l \<and> meets q l" (* by "affine_plane.a1" *)
  note `pm P (OrdinaryL l)` and `pm Q (OrdinaryL l)`

  show ?thesis sorry
next
  assume "n \<noteq> 0"
  show ?thesis sorry
qed


  sorry
(* Same deal: since pmeets IS the projectivization of "plmeets" above, which is an affine plane,
 and the previous theorem doesn't work, this one won't either, and indeed, "try" finds 
 the equivalent of affine_plane.plmeets as a counterexample. *)


end
