section \<open>Basic Transition System\<close>

theory Basic_Transition_System
  imports Relation_Methods.Equivalence Natural_Transition_Systems
begin

subsection \<open>Actions\<close>

text \<open>
  Actions include I/O actions and the internal action.
\<close>

datatype io_action =
  BasicOut \<open>chan\<close> \<open>val\<close> |
  BasicIn \<open>chan\<close> \<open>val\<close>
datatype basic_action =
  IO \<open>io_action\<close> |
  BasicInternal ("\<tau>")
abbreviation BasicOutAction :: "chan \<Rightarrow> val \<Rightarrow> basic_action" (infix "\<triangleleft>" 100) where
  "a \<triangleleft> x \<equiv> IO (BasicOut a x)"
abbreviation BasicInAction :: "chan \<Rightarrow> val \<Rightarrow> basic_action" (infix "\<triangleright>" 100) where
  "a \<triangleright> x \<equiv> IO (BasicIn a x)"

subsection \<open>Residuals\<close>

text \<open>
  There are two kinds of residuals in the basic transition system: acting residuals, written \<open>\<lbrace>\<alpha>\<rbrace> q\<close>
  where \<open>\<alpha>\<close> is an action, and scope opening residuals, written \<open>\<lbrace>\<nu> a\<rbrace> Q a\<close> where \<open>a\<close> is a channel
  variable.
\<close>

datatype 'p basic_residual =
  Acting \<open>basic_action\<close> \<open>'p\<close> ("\<lbrace>_\<rbrace> _" [0, 51] 51) |
  Opening \<open>chan \<Rightarrow> 'p\<close>
syntax
  "_Opening" :: "pttrn \<Rightarrow> process \<Rightarrow> 'p basic_residual"
  ("\<lbrace>\<nu> _\<rbrace> _" [0, 51] 51)
translations
  "\<lbrace>\<nu> a\<rbrace> p" \<rightleftharpoons> "CONST Opening (\<lambda>a. p)"
print_translation \<open>
  [Syntax_Trans.preserve_binder_abs_tr' @{const_syntax Opening} @{syntax_const "_Opening"}]
\<close>

text \<open>
  We introduce the alias \<open>basic_lift\<close> for the automatically generated relator
  \<^const>\<open>rel_basic_residual\<close>. Furthermore we provide alternative names for some facts related to
  \<open>basic_lift\<close>, which resemble the names that would be used for these facts if \<open>basic_lift\<close> was
  defined by hand via @{theory_text inductive}.
\<close>

abbreviation
  basic_lift :: "(['p, 'q] \<Rightarrow> bool) \<Rightarrow> (['p basic_residual, 'q basic_residual] \<Rightarrow> bool)"
where
  "basic_lift \<equiv> rel_basic_residual"

lemmas basic_lift_intros = basic_residual.rel_intros
lemmas acting_lift = basic_lift_intros(1)
lemmas opening_lift = basic_lift_intros(2)
lemmas basic_lift_cases = basic_residual.rel_cases

text \<open>
  Equipping \<^type>\<open>basic_residual\<close> with \<^const>\<open>basic_lift\<close> leads to a residual structure.
\<close>

interpretation basic: residual basic_lift
  by
    unfold_locales
    (
      fact basic_residual.rel_mono,
      fact basic_residual.rel_eq,
      fact basic_residual.rel_compp,
      fact basic_residual.rel_conversep
    )

subsection \<open>Communication\<close>

text \<open>
  Communication can be from left to right (output on the left, input on the right) and from right to
  left (input on the left, output on the right). We do not want to have two communication rules,
  which are analogous, and later have to handle these two rules separately in proofs. Therefore, we
  define a relation that tells which I/O action can pair with which other I/O action in a
  communication and have a single communication rule that uses this relation.
\<close>

inductive
  communication :: "io_action \<Rightarrow> io_action \<Rightarrow> bool"
  (infix "\<bowtie>" 50)
where
  ltr:
    "BasicOut a x \<bowtie> BasicIn a x" |
  rtl:
    "BasicIn a x \<bowtie> BasicOut a x"

text \<open>
  The communication relation is symmetric.
\<close>

lemma communication_symmetry_rule [sym]: "\<eta> \<bowtie> \<mu> \<Longrightarrow> \<mu> \<bowtie> \<eta>"
  by (blast elim: communication.cases intro: communication.intros)
lemma communication_symmetry: "symp (\<bowtie>)"
  using communication_symmetry_rule ..

subsection \<open>Transition System\<close>

text \<open>
  The following definition of the transition relation captures the set of rules that define the
  transition system.
\<close>

inductive
  basic_transition :: "process \<Rightarrow> process basic_residual \<Rightarrow> bool"
  (infix "\<rightarrow>\<^sub>\<flat>" 50)
where
  sending:
    "a \<triangleleft> x \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleleft> x\<rbrace> \<zero>" |
  receiving:
    "a \<triangleright> x. P x \<rightarrow>\<^sub>\<flat>\<lbrace>a \<triangleright> x\<rbrace> P x" |
  communication:
    "\<lbrakk> \<eta> \<bowtie> \<mu>; p \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'; q \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> q' \<rbrakk> \<Longrightarrow> p \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> p' \<parallel> q'" |
  opening:
    "\<nu> a. P a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a" |
  acting_left:
    "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p' \<Longrightarrow> p \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p' \<parallel> q" |
  acting_right:
    "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q' \<Longrightarrow> p \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p \<parallel> q'" |
  opening_left:
    "p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<Longrightarrow> p \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a \<parallel> q" |
  opening_right:
    "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<Longrightarrow> p \<parallel> q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> p \<parallel> Q a" |
  scoped_acting:
    "\<lbrakk> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a; \<And>a. Q a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> R a \<rbrakk> \<Longrightarrow> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. R a" |
  scoped_opening:
    "\<lbrakk> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a; \<And>a. Q a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> R a b \<rbrakk> \<Longrightarrow> p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. R a b"

text \<open>
  Note that \<open>scoped_acting\<close> and\<open>scoped_opening\<close> are the rules that perform closing.
\<close>

text \<open>
  The residual structure and \<^const>\<open>basic_transition\<close> together form a transition system.
\<close>

interpretation basic: transition_system basic_lift basic_transition
  by intro_locales

text \<open>
  We introduce concise notation for some of the derived predicates of the transition system.
\<close>

notation basic.pre_bisimilarity (infix "\<lesssim>\<^sub>\<flat>" 50)
notation basic.bisimilarity (infix "\<sim>\<^sub>\<flat>" 50)

subsection \<open>Fundamental Properties of the Transition System\<close>

text \<open>
  Edsko's \texttt{Com} rule can be simulated using a combination of \<open>opening_left\<close> (or, in the
  right-to-left case, \<open>opening_right\<close>), \<open>communication\<close>, and \<open>scoped_acting\<close>. Reordering of openings
  can be simulated using \<open>scoped_opening\<close>.
\<close>

text \<open>
  An acting and an opening version of the \texttt{Scope} rule in Edsko's definition can be derived
  by combining \<open>opening\<close> with the closing rules.
\<close>

lemma acting_scope: "(\<And>a. P a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q a) \<Longrightarrow> \<nu> a. P a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. Q a"
  using opening by (intro scoped_acting)
lemma opening_scope: "(\<And>a. P a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q a b) \<Longrightarrow> \<nu> a. P a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. Q a b"
  using opening by (intro scoped_opening)

text \<open>
  No transitions are possible from~\<open>\<zero>\<close>. This is not as trivial as it might seem, because also
  \<open>scoped_acting\<close> and \<open>scoped_opening\<close> have to be taken into account.
\<close>

lemma no_basic_transitions_from_stop: "\<not> \<zero> \<rightarrow>\<^sub>\<flat>c"
proof
  fix c
  assume "\<zero> \<rightarrow>\<^sub>\<flat>c"
  then show False by (induction "\<zero>" c)
qed

text \<open>
  Only certain transitions are possible from send and receive processes.
\<close>

lemma basic_transitions_from_send: "a \<triangleleft> x \<rightarrow>\<^sub>\<flat>c \<Longrightarrow> c = \<lbrace>a \<triangleleft> x\<rbrace> \<zero>"
proof -
  fix a and x and c
  assume "a \<triangleleft> x \<rightarrow>\<^sub>\<flat>c"
  then show "c = \<lbrace>a \<triangleleft> x\<rbrace> \<zero>"
  proof (induction "a \<triangleleft> x :: process" c)
    case sending
    show ?case by (fact refl)
  next
    case scoped_acting
    then show ?case by simp
  next
    case scoped_opening
    then show ?case by simp
  qed
qed
lemma basic_transitions_from_receive:
  assumes "a \<triangleright> x. P x \<rightarrow>\<^sub>\<flat>c"
  obtains x where "c = \<lbrace>a \<triangleright> x\<rbrace> P x"
using assms proof (induction "a \<triangleright> x. P x" c)
  case receiving
  then show ?case by simp
next
  case scoped_acting
  then show ?case by blast
next
  case scoped_opening
  then show ?case by blast
qed

text \<open>
  No opening transitions are possible from send and receive processes.
\<close>

lemma no_opening_transitions_from_send: "\<not> a \<triangleleft> x \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b"
  using basic_transitions_from_send by blast
lemma no_opening_transitions_from_receive: "\<not> a \<triangleright> x. P x \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> Q b"
  using basic_transitions_from_receive by blast

subsection \<open>Proof Tools\<close>

(* NOTE:
  The following code is introduced only temporarily to make the bisimilarity proofs below work with
  the refactored simulation system methods. It will be removed as part of resolving #78.
*)
method old_bisimilarity_standard for \<X> :: "[process, process] \<Rightarrow> bool" = (
  (
    intro predicate2D [of \<X> "(\<sim>\<^sub>\<flat>)", rotated];
      match conclusion in
        "\<X> _ _" (cut) \<Rightarrow> \<open>succeed\<close> \<bar>
        "\<X> \<le> (\<sim>\<^sub>\<flat>)" (cut) \<Rightarrow> \<open>
          (match premises in prems [thin]: _ (cut, multi) \<Rightarrow> \<open>succeed\<close> | succeed);
            (
              intro basic.bisimulation_in_bisimilarity,
              intro basic.symmetric_simulation_is_bisimulation
            );
              match conclusion in
                "symp \<X>" (cut) \<Rightarrow> \<open>intro sympI\<close> \<bar>
                "basic.sim \<X>" (cut) \<Rightarrow> \<open>basic.is_simulation_standard\<close>
        \<close>
  ),
  goal_cases related sym sim
)

context begin

private lemma sim_scoped_acting_intro:
  assumes with_new_channel:
    "\<And>P Q. (\<And>a. \<X> (P a) (Q a)) \<Longrightarrow> \<X> (\<nu> a. P a) (\<nu> a. Q a)"
  assumes step_1:
    "\<And>t. \<X> s t \<Longrightarrow> \<exists>d\<^sub>1. t \<rightarrow>\<^sub>\<flat>d\<^sub>1 \<and> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> S\<^sub>1 a) d\<^sub>1"
  assumes step_2:
    "\<And>a t\<^sub>1. \<X> (S\<^sub>1 a) t\<^sub>1 \<Longrightarrow> \<exists>d\<^sub>2. t\<^sub>1 \<rightarrow>\<^sub>\<flat>d\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<alpha>\<rbrace> S\<^sub>2 a) d\<^sub>2"
  assumes initial_relation:
    "\<X> s t"
  shows
    "\<exists>d\<^sub>2. t \<rightarrow>\<^sub>\<flat>d\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<alpha>\<rbrace> \<nu> a. S\<^sub>2 a) d\<^sub>2"
proof -
  from step_1 and \<open>\<X> s t\<close>
  obtain T\<^sub>1 where "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and "\<And>a. \<X> (S\<^sub>1 a) (T\<^sub>1 a)"
    using
      basic_lift_cases and
      rel_funE and
      basic_residual.distinct(1) and
      basic_residual.inject(2)
    by smt
  obtain T\<^sub>2 where "\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a" and "\<And>a. \<X> (S\<^sub>2 a) (T\<^sub>2 a)"
  proof -
    from step_2 and \<open>\<And>a. \<X> (S\<^sub>1 a) (T\<^sub>1 a)\<close>
    have "\<forall>a. \<exists>v. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> v \<and> \<X> (S\<^sub>2 a) v"
      using
        basic_lift_cases and
        rel_funE and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then have "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a \<and> \<X> (S\<^sub>2 a) (T\<^sub>2 a)"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from \<open>t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a\<close> and \<open>\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> T\<^sub>2 a\<close> have "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. T\<^sub>2 a"
    by (fact basic_transition.scoped_acting)
  with \<open>\<And>a. \<X> (S\<^sub>2 a) (T\<^sub>2 a)\<close> show ?thesis
    using with_new_channel and acting_lift
    by smt
qed

private lemma sim_scoped_opening_intro:
  assumes with_new_channel:
    "\<And>P Q. (\<And>a. \<X> (P a) (Q a)) \<Longrightarrow> \<X> (\<nu> a. P a) (\<nu> a. Q a)"
  assumes step_1:
    "\<And>t. \<X> s t \<Longrightarrow> \<exists>d\<^sub>1. t \<rightarrow>\<^sub>\<flat>d\<^sub>1 \<and> basic_lift \<X> (\<lbrace>\<nu> a\<rbrace> S\<^sub>1 a) d\<^sub>1"
  assumes step_2:
    "\<And>a t\<^sub>1. \<X> (S\<^sub>1 a) t\<^sub>1 \<Longrightarrow> \<exists>d\<^sub>2. t\<^sub>1 \<rightarrow>\<^sub>\<flat>d\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<nu> b\<rbrace> S\<^sub>2 a b) d\<^sub>2"
  assumes initial_relation:
    "\<X> s t"
  shows
    "\<exists>d\<^sub>2. t \<rightarrow>\<^sub>\<flat>d\<^sub>2 \<and> basic_lift \<X> (\<lbrace>\<nu> b\<rbrace> \<nu> a. S\<^sub>2 a b) d\<^sub>2"
proof -
  from step_1 and \<open>\<X> s t\<close>
  obtain T\<^sub>1 where "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a" and "\<And>a. \<X> (S\<^sub>1 a) (T\<^sub>1 a)"
    using
      basic_lift_cases and
      rel_funE and
      basic_residual.distinct(1) and
      basic_residual.inject(2)
    by smt
  obtain T\<^sub>2 where "\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b" and "\<And>a b. \<X> (S\<^sub>2 a b) (T\<^sub>2 a b)"
  proof -
    from step_2 and \<open>\<And>a. \<X> (S\<^sub>1 a) (T\<^sub>1 a)\<close>
    have "\<forall>a. \<exists>V. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> V b \<and> (\<forall>b. \<X> (S\<^sub>2 a b) (V b))"
      using
        basic_lift_cases and
        rel_funE and
        basic_residual.distinct(1) and
        basic_residual.inject(2)
      by smt
    then have "\<exists>T\<^sub>2. \<forall>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b \<and> (\<forall>b. \<X> (S\<^sub>2 a b) (T\<^sub>2 a b))"
      by (fact choice)
    with that show ?thesis by blast
  qed
  from \<open>t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> T\<^sub>1 a\<close> and \<open>\<And>a. T\<^sub>1 a \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> T\<^sub>2 a b\<close> have "t \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. T\<^sub>2 a b"
    by (fact basic_transition.scoped_opening)
  with \<open>\<And>a b. \<X> (S\<^sub>2 a b) (T\<^sub>2 a b)\<close> show ?thesis
    using with_new_channel and opening_lift and rel_funI
    by smt
qed

private method solve_sim_scoped uses with_new_channel = (
  match conclusion in
    "\<exists>d\<^sub>2. _ \<rightarrow>\<^sub>\<flat>d\<^sub>2 \<and> basic_lift _ (\<lbrace>_\<rbrace> \<nu> a. _ a) d\<^sub>2" (cut) \<Rightarrow> \<open>
      match premises in "s \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> S\<^sub>1 a" for s and S\<^sub>1 \<Rightarrow> \<open>
        match premises in prems [thin]: _ (multi) \<Rightarrow> \<open>
          intro sim_scoped_acting_intro [where s = s and S\<^sub>1 = S\<^sub>1],
          simp add: with_new_channel,
          simp_all add: prems
        \<close>
      \<close>
    \<close> \<bar>
    "\<exists>d\<^sub>2. _ \<rightarrow>\<^sub>\<flat>d\<^sub>2 \<and> basic_lift _ (\<lbrace>\<nu> b\<rbrace> \<nu> a. _ a b) d\<^sub>2" (cut) \<Rightarrow> \<open>
      match premises in "s \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> S\<^sub>1 a" for s and S\<^sub>1 \<Rightarrow> \<open>
        match premises in prems [thin]: _ (multi) \<Rightarrow> \<open>
          intro sim_scoped_opening_intro [where s = s and S\<^sub>1 = S\<^sub>1],
          simp add: with_new_channel,
          simp_all add: prems
        \<close>
      \<close>
    \<close> \<bar>
    _ (cut) \<Rightarrow> \<open>succeed\<close>
)

method basic_sim_induction for t uses with_new_channel =
  (induction arbitrary: t; solve_sim_scoped with_new_channel: with_new_channel)

end

subsection \<open>The Basic Transition System as a Natural Transition System\<close>

context begin

private lemma basic_pre_receive_preservation: "(\<And>x. P x \<sim>\<^sub>\<flat> Q x) \<Longrightarrow> a \<triangleright> x. P x \<lesssim>\<^sub>\<flat> a \<triangleright> x. Q x"
proof (standard, intro allI, intro impI)
  assume "\<And>x. P x \<sim>\<^sub>\<flat> Q x"
  fix c
  assume "a \<triangleright> x. P x \<rightarrow>\<^sub>\<flat>c"
  then show "\<exists>d. a \<triangleright> x. Q x \<rightarrow>\<^sub>\<flat>d \<and> basic_lift (\<lambda>p q. p \<lesssim>\<^sub>\<flat> q \<and> q \<lesssim>\<^sub>\<flat> p) c d"
  proof cases
    case receiving
    with \<open>\<And>x. P x \<sim>\<^sub>\<flat> Q x\<close> show ?thesis
      unfolding basic.bisimilarity_def
      using basic_transition.receiving and acting_lift
      by (metis (no_types, lifting))
  qed (simp_all add: no_opening_transitions_from_receive)
qed

lemma basic_receive_preservation: "(\<And>x. P x \<sim>\<^sub>\<flat> Q x) \<Longrightarrow> a \<triangleright> x. P x \<sim>\<^sub>\<flat> a \<triangleright> x. Q x"
  by (simp add: basic_pre_receive_preservation basic.bisimilarity_def)

end

context begin

private inductive
  parallel_preservation_left_aux :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel: "
    p \<sim>\<^sub>\<flat> q \<Longrightarrow> parallel_preservation_left_aux (p \<parallel> r) (q \<parallel> r)" |
  with_new_channel: "
    (\<And>a. parallel_preservation_left_aux (S a) (T a)) \<Longrightarrow>
    parallel_preservation_left_aux (\<nu> a. S a) (\<nu> a. T a)"

lemma basic_parallel_preservation_left: "p \<sim>\<^sub>\<flat> q \<Longrightarrow> p \<parallel> r \<sim>\<^sub>\<flat> q \<parallel> r"
proof (old_bisimilarity_standard parallel_preservation_left_aux)
  case related
  then show ?case by (fact parallel_preservation_left_aux.without_new_channel)
next
  case sym
  then show ?case
    by induction (simp_all add: basic.bisimilarity_def parallel_preservation_left_aux.intros)
next
  case (sim s t c)
  then show ?case
  proof (basic_sim_induction t with_new_channel: parallel_preservation_left_aux.with_new_channel)
    case (communication \<eta> \<mu> p p' r r' t)
    from communication.prems show ?case
    proof cases
      case (without_new_channel q)
      from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> p'\<close> obtain q' where "q \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> q'" and "p' \<sim>\<^sub>\<flat> q'"
        unfolding basic.bisimilarity_def
        using 
          basic.pre_bisimilarity.cases and
          basic_residual.inject(1) and
          basic_residual.distinct(2) and
          basic_lift_cases
        by smt
      from \<open>\<eta> \<bowtie> \<mu>\<close> and \<open>q \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> q'\<close> and \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> r'\<close> have "q \<parallel> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> q' \<parallel> r'"
        by (fact basic_transition.communication)
      with \<open>t = q \<parallel> r\<close> and \<open>p' \<sim>\<^sub>\<flat> q'\<close> show ?thesis
        using parallel_preservation_left_aux.without_new_channel and acting_lift
        by auto
    qed
  next
    case opening
    from opening.prems show ?case
    proof cases
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lift and rel_funI
        by (metis (full_types))
    qed
  next
    case (acting_left p \<alpha> p' r t)
    from acting_left.prems show ?case
    proof cases
      case (without_new_channel q)
      from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> p'\<close> obtain q' where "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q'" and "p' \<sim>\<^sub>\<flat> q'"
        unfolding basic.bisimilarity_def
        using 
          basic.pre_bisimilarity.cases and
          basic_residual.inject(1) and
          basic_residual.distinct(2) and
          basic_lift_cases
        by smt
      from \<open>q \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q'\<close> have "q \<parallel> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> q' \<parallel> r"
        by (fact basic_transition.acting_left)
      with \<open>t = q \<parallel> r\<close> and \<open>p' \<sim>\<^sub>\<flat> q'\<close> show ?thesis
        using parallel_preservation_left_aux.without_new_channel and acting_lift
        by auto
    qed
  next
    case acting_right
    from acting_right.prems show ?case
    proof cases
      case without_new_channel
      with acting_right.hyps show ?thesis
        using
          basic_transition.acting_right and
          parallel_preservation_left_aux.without_new_channel and
          acting_lift
        by metis
    qed
  next
    case (opening_left p P r t)
    from opening_left.prems show ?case
    proof cases
      case (without_new_channel q)
      from \<open>p \<sim>\<^sub>\<flat> q\<close> and \<open>p \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P a\<close>
      obtain Q where "q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a" and "\<And>a. P a \<sim>\<^sub>\<flat> Q a"
        unfolding basic.bisimilarity_def
        by (force elim: basic.pre_bisimilarity.cases basic_lift_cases rel_funE)
      from \<open>q \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a\<close> have "q \<parallel> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> Q a \<parallel> r"
        by (fact basic_transition.opening_left)
      with \<open>t = q \<parallel> r\<close> and \<open>\<And>a. P a \<sim>\<^sub>\<flat> Q a\<close> show ?thesis
        using
          parallel_preservation_left_aux.without_new_channel and
          opening_lift and
          rel_funI
        by smt
    qed
  next
    case (opening_right r R p t)
    from opening_right.prems show ?case
    proof cases
      case (without_new_channel q)
      from \<open>r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> R a\<close> have "q \<parallel> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> q \<parallel> R a"
        by (fact basic_transition.opening_right)
      from \<open>p \<sim>\<^sub>\<flat> q\<close> have "\<And>a. parallel_preservation_left_aux (p \<parallel> R a) (q \<parallel> R a)"
        by (fact parallel_preservation_left_aux.without_new_channel)
      with \<open>t = q \<parallel> r\<close> and \<open>q \<parallel> r \<rightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> q \<parallel> R a\<close> show ?thesis
        using opening_lift and rel_funI
        by smt
    qed
  qed (blast elim: parallel_preservation_left_aux.cases)+
qed

end

lemma basic_parallel_preservation_right: "q\<^sub>1 \<sim>\<^sub>\<flat> q\<^sub>2 \<Longrightarrow> p \<parallel> q\<^sub>1 \<sim>\<^sub>\<flat> p \<parallel> q\<^sub>2"
  sorry

lemma basic_parallel_preservation: "\<lbrakk>p\<^sub>1 \<sim>\<^sub>\<flat> p\<^sub>2; q\<^sub>1 \<sim>\<^sub>\<flat> q\<^sub>2\<rbrakk> \<Longrightarrow> p\<^sub>1 \<parallel> q\<^sub>1 \<sim>\<^sub>\<flat> p\<^sub>2 \<parallel> q\<^sub>2"
  sorry

context begin

private inductive
  new_channel_preservation_aux :: "process \<Rightarrow> process \<Rightarrow> bool"
where
  without_new_channel: "
    p \<sim>\<^sub>\<flat> q \<Longrightarrow> new_channel_preservation_aux p q" |
  with_new_channel: "
    (\<And>a. new_channel_preservation_aux (S a) (T a)) \<Longrightarrow>
    new_channel_preservation_aux (\<nu> a. S a) (\<nu> a. T a)"

private method new_channel_preservation_aux_trivial_conveyance =
  (smt
    basic.bisimilarity_def
    basic.pre_bisimilarity.cases
    new_channel_preservation_aux.without_new_channel
    basic.lift_monotonicity
    predicate2I
    predicate2D)

lemma basic_new_channel_preservation: "(\<And>a. P a \<sim>\<^sub>\<flat> Q a) \<Longrightarrow> \<nu> a. P a \<sim>\<^sub>\<flat> \<nu> a. Q a"
proof (old_bisimilarity_standard new_channel_preservation_aux)
  case related
  then show ?case by (simp add: new_channel_preservation_aux.intros)
next
  case sym
  then show ?case
    by induction (simp_all add: basic.bisimilarity_def new_channel_preservation_aux.intros)
next
  case (sim s t c)
  from this and \<open>s \<rightarrow>\<^sub>\<flat>c\<close> show ?case
  proof (basic_sim_induction t with_new_channel: new_channel_preservation_aux.with_new_channel)
    case sending
    from sending.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case receiving
    from receiving.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case communication
    from communication.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case opening
    from opening.prems show ?case
    proof cases
      case with_new_channel
      then show ?thesis
        using basic_transition.opening and opening_lift
        by blast
    qed new_channel_preservation_aux_trivial_conveyance
  next
    case acting_left
    from acting_left.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case acting_right
    from acting_right.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case opening_left
    from opening_left.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  next
    case opening_right
    from opening_right.prems show ?case
      by cases new_channel_preservation_aux_trivial_conveyance
  qed
qed

end

interpretation basic: natural_transition_system basic_lift basic_transition
  by
    unfold_locales
    (
      fact basic_receive_preservation,
      fact basic_parallel_preservation,
      fact basic_new_channel_preservation
    )

subsection \<open>Setup of the @{method equivalence} Proof Method\<close>

quotient_type basic_behavior = process / "(\<sim>\<^sub>\<flat>)"
  using basic.bisimilarity_is_equivalence .

declare basic_behavior.abs_eq_iff [equivalence_transfer]

context begin

private lift_definition stop' :: basic_behavior
  is Stop .

private lift_definition send' :: "[chan, val] \<Rightarrow> basic_behavior"
  is Send .

private lift_definition receive' :: "[chan, val \<Rightarrow> basic_behavior] \<Rightarrow> basic_behavior"
  is Receive
  using basic_receive_preservation .

private lift_definition parallel' :: "[basic_behavior, basic_behavior] \<Rightarrow> basic_behavior"
  is Parallel
  using basic_parallel_preservation .

private lift_definition new_channel' :: "(chan \<Rightarrow> basic_behavior) \<Rightarrow> basic_behavior"
  is NewChannel
  using basic_new_channel_preservation .

private lift_definition guard' :: "[bool, basic_behavior] \<Rightarrow> basic_behavior"
  is guard
  using basic.guard_preservation .

private lift_definition general_parallel' :: "['a \<Rightarrow> basic_behavior, 'a list] \<Rightarrow> basic_behavior"
  is general_parallel
  using basic.general_parallel_preservation .

lemmas [equivalence_transfer] =
  stop'.abs_eq
  send'.abs_eq
  receive'.abs_eq
  parallel'.abs_eq
  new_channel'.abs_eq
  guard'.abs_eq
  general_parallel'.abs_eq

end

subsection \<open>Conclusion\<close>

text \<open>
  This is all for the basic transition system.
\<close>

end
