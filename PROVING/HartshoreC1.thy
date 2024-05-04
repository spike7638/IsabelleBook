theory Chapter1
  imports Complex_Main

begin


(* an attempt, using a stack-exchange posting, to make sledgehammer more informative.

sledgehammer_params[minimize=true,preplay_timeout=10,timeout=60,verbose=true,
                    provers="
  vampire     cvc4 spass  
      e        z3       
"] 
*)

  text \<open>
Contents:
\<^item> We formalize the first chapter of Hartshorne's "Projective Geometry"
\<^item> Propositions like "1.1" in the text are given names like Prop1P1 (with "P" replacing the 
decimal point)
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

  (* PAGE 2 *)
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

  (* PAGE 3, slightly out of order *)
  lemma symmetric_parallel: "l || m \<Longrightarrow> m || l"
    using parallel_def by auto

  lemma reflexive_parallel: "l || l"
    by (simp add: parallel_def)

  lemma transitive_parallel: "\<lbrakk>l || m ;  m || n\<rbrakk> \<Longrightarrow> l || n"
    by (metis a2 parallel_def)
  end

section {* The real affine plane *}
text{* Hartshorne mentions the ordinary affine plane as an example of a plane. We should prove 
that it's actually an affine plane. It's pretty clear how to represent points --- pairs of real 
numbers --- but what about lines? A line is the set of points satisfying an equation of 
the form Ax + By + C = 0, with not both of A and B being zero. The problem is that there's 
no datatype for "pair of real numbers, at least one of which is nonzero". We'll have 
to hack this by breaking lines into "ordinary" and "vertical", alas.   *}

  datatype a2pt = A2Point "real" "real"

  datatype a2ln = A2Ordinary "real" "real" 
                | A2Vertical "real"
  text "Ordinary m b represents the line y = mx+b; Vertical xo is the line x = xo "

  fun a2meets :: "a2pt \<Rightarrow> a2ln \<Rightarrow> bool" where
    "a2meets (A2Point x y) (A2Ordinary m b) = (y = m*x + b)" |
    "a2meets (A2Point x y) (A2Vertical xi) = (x = xi)"


  text{* Now some small lemmas, basically establishing the three axioms *}
  text{* I'm going to venture into a new style of writing theorems and proofs, one that's
particularly applicable when you're showing something exists by constructing it. Here is 
an example in the case of real numbers: if r < s, then there's a real number strictly between
them. We could write this as "r < s \<Longrightarrow> \<exists> t . ((r < t) \<and> (t < s))" (although it turns out we'd have
to start with "(r::real) < s ..." to tell Isar not to assume that r is a natural number -- after all, 
this is one of those cases where type-inference has no idea whether "<" means less-than on the reals,
or the integers, or the natural numbers, or ...)

Anyhow, in this new style, we would write the theorem like this:

theorem mid:
  fixes r :: real
  assumes lt : "r < s"
  shows "\<exists>t. r < t \<and> t < s"
proof
  let ?t = "(r + s) / 2"
  from lt show "r < ?t \<and> ?t < s" by simp
qed

The nice thing about this style is that it takes care of "fix"ing things in the theorem statement,
and takes care of assuming the antecedent (which we always end up doing in the proof anyhow), and
then makes clear what we're going to actually show. We will treat this as a pattern henceforth *}


lemma A2_a1a: 
  fixes P :: a2pt
  fixes Q
  assumes "P \<noteq> Q"
  shows "\<exists> ls . a2meets P ls \<and> a2meets Q ls"
proof (cases P)
  case P: (A2Point x0 y0)
  then show ?thesis
  proof (cases Q)
    case Q: (A2Point x1 y1)
    then show ?thesis
    proof (cases "(x0 = x1)")
      case True
      assume f: "x0 = x1"
      have x1x0: "x1 = x0" by (simp add: True)
      let ?ll = "A2Vertical x0"
      have m1:  "a2meets P ?ll" using P  by simp
      have m2:  "a2meets Q ?ll" using Q  by (simp add: x1x0)
      thus ?thesis using m1 by blast (* We've proved the theorem...in the case where x0 = x1 *)           
  next
    case False (* Now on to the other case, where x0 \<noteq> x1; we'll need to divide by x1 - x0...*)
    assume f: "x0 \<noteq> x1"
    have x0x1: "x1 \<noteq> x0" using f by blast
    have x01 : "x1 - x0  \<noteq> 0" using x0x1 by simp 
    let ?ll = "A2Ordinary ((y1-y0)/(x1-x0))  (y0 - ((y1-y0)/(x1-x0))*x0) "
    (* we want to show that P and Q are both on ll; P is easy for some reason; Q is not *)
    have m3:  "a2meets P ?ll" using P  by simp

    have s2: "((y1-y0)/(x1 - x0))* x1 + (y0 - ((y1-y0)/(x1 - x0) )*x0) = ((y1-y0) * x1/(x1 - x0)) + (y0 - ((y1-y0)/(x1 - x0) )*x0)" by simp
    also have s3 : "... =  ((y1-y0) * x1/(x1 - x0)) + (y0 - ((y1-y0)*x0/(x1 - x0) ))" by simp
    also have s4 : "... =  ((y1*x1-y0*x1) /(x1 - x0)) + (y0 - ((y1*x0-y0*x0)/(x1 - x0) ))" by argo
    also have s5 : "... =  ((y1*x1-y0*x1) /(x1 - x0)) + (y0*(x1 - x0)/(x1-x0) - ((y1*x0-y0*x0)/(x1 - x0) ))" using x01 by simp
    also have s6 : "... =  ((y1*x1-y0*x1) /(x1 - x0)) + ((y0*x1 - y0*x0)/(x1-x0) - ((y1*x0-y0*x0)/(x1 - x0) ))" by argo
    also have s7 : "... =  (y1*x1-y0*x1) /(x1 - x0) + ((y0*x1 - y0*x0) - (y1*x0-y0*x0))/(x1 - x0) " by argo
    also have s8 : "... =  ((y1*x1-y0*x1) + (y0*x1 - y0*x0) - (y1*x0-y0*x0))/(x1 - x0) " by argo
    also have s9 : "... =  (y1*x1-y0*x1 + y0*x1 - y0*x0 - y1*x0+y0*x0)/(x1 - x0) " by argo
    also have s10 : "... =  (y1*x1 - y0*x0 - y1*x0+y0*x0)/(x1 - x0) " by argo
    also have s11 : "... =  (y1*x1  - y1*x0)/(x1 - x0) " by argo
    also have s12 : "... =  (y1*(x1  - x0))/(x1 - x0) " by argo
    also have s13 : "... =  y1 " using x01 by simp
    finally have s14: "((y1-y0)/(x1 - x0))* x1 + (y0 - ((y1-y0)/(x1 - x0) )*x0) = y1" .
    moreover have m4:  "a2meets Q ?ll" using s14 by (simp add: Q)
    show ?thesis using m3 m4 by auto
    qed
  qed
qed

(* An alternative proof for A@_2_a1a, buy Eugene Stark, who manages to take larger steps between
equations:

theorem A2_a1a:
  assumes "P \<noteq> Q"
  shows "\<exists> ls . a2meets P ls \<and> a2meets Q ls"
  proof (cases P, cases Q)
    fix x0 y0 x1 y1
    assume P: "P = A2Point x0 y0" and Q: "Q = A2Point x1 y1"
    show "\<exists> ls . a2meets P ls \<and> a2meets Q ls"
    proof (cases "x0 = x1")
      assume 1: "x0 = x1"
      have "a2meets P (A2Vertical x0) \<and> a2meets Q (A2Vertical x0)"
        using P Q 1 by simp
      thus "\<exists> ls . a2meets P ls \<and> a2meets Q ls" by blast
      next
      assume 2: "x0 \<noteq> x1"
      let ?ll = "A2Ordinary ((y1-y0)/(x1-x0)) (y0 - ((y1-y0)/(x1-x0))*x0)"
      have "a2meets P ?ll" using P by simp
      moreover have "a2meets Q ?ll"
      proof -
        have "y1 = (y1 - y0) * x1 / (x1 - x0) + (y0 - (y1 - y0) * x0 / (x1 - x0))"
        proof -
          have "y1 = (y1 * (x1 - x0)) / (x1 - x0)"
            using 2 by simp
          also have "... = (y1 - y0) * x1 / (x1 - x0) +
                           (y0 * (x1 - x0) / (x1 - x0) - (y1 - y0) * x0 / (x1 - x0))"
            by argo
          also have "... = (y1 - y0) * x1 / (x1 - x0) + (y0 - (y1 - y0) * x0 / (x1 - x0))"
            using 2 by simp
          finally show ?thesis by blast
        qed
        thus ?thesis
          using 2 Q by simp
      qed
      ultimately show ?thesis by blast
    qed
  qed
*)
  text{*For this next theorem, it might make sense to phrase it as 
lemma a1b: "P \<noteq> Q \<Longrightarrow> \<exists>! l . a2meets P l \<and> a2meets Q l", i.e., as the final result,
but that would require proving the existence of l (which we just did in the previous lemma) and
then proving that it's unique. Instead, we can just say that if l and m both contain the 
distinct points P and Q, then l must equal m. From this, and the previous lemma, we can then 
conclude that axiom 1 is true (which we'll do in a final theorem). 
 *}

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
  proof (cases P)
    case (A2Point x0 y0)
    then show ?thesis
    proof (cases Q)
      case (A2Point x1 y1)
      have ?thesis 
      proof (cases l)
        case (A2Ordinary s1 b1) (* l is ordinary *)
        assume lo: "l = A2Ordinary s1 b1"
        then show ?thesis 
        proof (cases m) (* Handle m ordinary, vertical in two steps *)
          case (A2Ordinary s2 b2)
          then show ?thesis by (smt A2Point a2ln.inject(1) a2meets.elims(2) a2meets.simps(1) a2pt.inject crossproduct_noteq lo pl pm pq ql qm)
        next
          case (A2Vertical x2)
          then have ?thesis using A2Point a2meets.elims(2) pl pm pq ql qm by fastforce
          show ?thesis by (simp add: \<open>l = m\<close>)
        qed
      next
        case (A2Vertical x2) (* l is vertical *)
        then show ?thesis by (smt a2ln.inject(1) a2meets.elims(2) a2meets.simps(2) pl pm pq ql qm)
      qed
      show ?thesis by (simp add: \<open>l = m\<close>)
    qed
  qed

(* 
(*
Now here's a proof of axiom 1; it involves a bunch of steps. What's funny is that the proof 
(uncommented-out) below uses almost nothing. It's discovered by stating  the theorem, and try typing
'try', like this:
====
theorem a1 : "P \<noteq> Q \<Longrightarrow> \<exists>! l . a2meets P l \<and> a2meets Q l"
try
====
Once you go into "proof -" mode, that no longer works, alas, so you end up travelling down 
this route.
*)
theorem a1 : "P \<noteq> Q \<Longrightarrow> \<exists>! l . a2meets P l \<and> a2meets Q l"
proof -
  try
  assume "P \<noteq> Q"
  show ?thesis
  proof (cases P)
    case (A2Point x0 y0)
    then show ?thesis 
    proof (cases Q)
      case (A2Point x1 y1)
      have ?thesis using \<open>P \<noteq> Q\<close> a1a a1b by blast
      show ?thesis by (simp add: \<open>\<exists>!l. a2meets P l \<and> a2meets Q l\<close>)
    qed
  qed
qed
*)
  theorem a1 : "P \<noteq> Q \<Longrightarrow> \<exists>! l . a2meets P l \<and> a2meets Q l"
    using A2_a1a A2_a1b by blast

theorem A2_a3a: "(\<nexists> m. a2meets (A2Point 0 0) m \<and> a2meets (A2Point 0 1) m \<and> a2meets (A2Point 1 0) m)"
  proof 
    let ?P = "A2Point 0 0"
    let ?Q = "A2Point 1 0"
    let ?R = "A2Point 0 1"
    have pr : "?P \<noteq> ?R" by (auto)
    have pq : "?P \<noteq> ?Q" by (auto)
    have qr : "?Q \<noteq> ?R" by (auto)
    show "(\<nexists> m. a2meets ?P m \<and> a2meets ?Q m \<and> a2meets ?R m)" 
      try

theorem "affine_plane a2meets" by
  by (simp add: affine_plane.intro) 

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
    (* NB : We have not actually split into cases here, but rather just prove directly that l || m 
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
  (* proposition five_points_necessary: "\<exists>A::'point set. finite A \<and> card A = 5"
    by nitpick
  oops *)
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
  (* an example of testing the truth of some assertion using "value": *)
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
      moreover  "pm Q (OrdinaryL lo)" by sorry 
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


