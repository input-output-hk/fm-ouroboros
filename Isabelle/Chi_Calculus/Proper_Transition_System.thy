section \<open>Proper Transition System\<close>

theory Proper_Transition_System
  imports Basic_Transition_System
begin

subsection \<open>Actions\<close>

text \<open>
  Actions include input actions and the silent action.
\<close>

datatype proper_action =
  ProperIn chan val (infix "\<triangleright>" 100) |
  ProperSilent ("\<tau>")

text \<open>
  Each action in the proper transition system corresponds to an action in the basic transition
  system.
\<close>

primrec basic_action_of :: "proper_action \<Rightarrow> basic_action" where
  "basic_action_of (c \<triangleright> V) = c \<triangleright> V" |
  "basic_action_of \<tau> = \<tau>"

subsection \<open>Output Rests\<close>

text \<open>
  An output rest bundles the scope openings, the output value, and the target process of an output
  transition. Its syntax is part of the syntax of output transitions.
\<close>

datatype output_rest =
  WithoutOpening val process ("_\<rparr> _" [52, 51] 51) |
  WithOpening "(chan \<Rightarrow> output_rest)" (binder "\<nu>" 51)

text \<open>
  Note that the definition of \<open>output_rest\<close> is actually more permissive than the verbal definition
  of output rests above: the number of scope openings of a particular \<open>output_rest\<close> value is not
  necessarily fixed, since the structure of a follow-up output rest in a \<open>WithOpening\<close> value can
  depend on the given channel. This is just to keep the definition simple. It does not cause any
  problems in our later proofs.
\<close>

text \<open>
  There is a notion of output rest lifting on which the definition of residual lifting is based.
\<close>

inductive
  output_rest_lift :: "(process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> (output_rest \<Rightarrow> output_rest \<Rightarrow> bool)"
  for \<X>
where
  without_opening_lift:
    "\<X> P Q \<Longrightarrow> output_rest_lift \<X> (V\<rparr> P) (V\<rparr> Q)" |
  with_opening_lift:
    "(\<And>a. output_rest_lift \<X> (\<K> a) (\<L> a)) \<Longrightarrow> output_rest_lift \<X> (\<nu> a. \<K> a) (\<nu> a. \<L> a)"

text \<open>
  Interestingly, the \<^const>\<open>output_rest_lift\<close> operator has the properties of a residual lifting
  operator, despite the fact that output rests are not intended to serve as residuals but only as
  components of residuals.
\<close>

lemma output_rest_lift_monotonicity:
  "\<X> \<le> \<Y> \<Longrightarrow> output_rest_lift \<X> \<le> output_rest_lift \<Y>"
proof
  fix K and L
  assume "output_rest_lift \<X> K L" and "\<X> \<le> \<Y>"
  then show "output_rest_lift \<Y> K L" by induction (blast intro: output_rest_lift.intros)+
qed
lemma output_rest_lift_equality_preservation:
  "output_rest_lift op = = op ="
proof (intro ext)
  fix K\<^sub>1 and K\<^sub>2
  show "output_rest_lift op = K\<^sub>1 K\<^sub>2 \<longleftrightarrow> K\<^sub>1 = K\<^sub>2"
  proof
    assume "output_rest_lift op = K\<^sub>1 K\<^sub>2"
    then show "K\<^sub>1 = K\<^sub>2"
      by induction (simp_all add: ext)
  next
    assume "K\<^sub>1 = K\<^sub>2"
    then show "output_rest_lift op = K\<^sub>1 K\<^sub>2"
      by (induction K\<^sub>1 arbitrary: K\<^sub>2) (blast intro: output_rest_lift.intros)+
  qed
qed
lemma output_rest_lift_composition_preservation:
  "output_rest_lift (\<X> OO \<Y>) = output_rest_lift \<X> OO output_rest_lift \<Y>"
proof (intro ext)
  fix K and M
  show "output_rest_lift (\<X> OO \<Y>) K M \<longleftrightarrow> (output_rest_lift \<X> OO output_rest_lift \<Y>) K M"
  proof
    assume "output_rest_lift (\<X> OO \<Y>) K M"
    then show "(output_rest_lift \<X> OO output_rest_lift \<Y>) K M"
    proof induction
      case (without_opening_lift P R V)
      then obtain Q where "\<X> P Q" and "\<Y> Q R" by (elim relcomppE)
      then show ?case by (blast intro: output_rest_lift.without_opening_lift)
    next
      case (with_opening_lift \<K> \<M>)
      obtain \<L> where "\<And>a. output_rest_lift \<X> (\<K> a) (\<L> a)" and "\<And>a. output_rest_lift \<Y> (\<L> a) (\<M> a)"
      proof -
        from `\<And>a. (output_rest_lift \<X> OO output_rest_lift \<Y>) (\<K> a) (\<M> a)`
        have "\<forall>a. \<exists>L. output_rest_lift \<X> (\<K> a) L \<and> output_rest_lift \<Y> L (\<M> a)"
          by blast
        then have "\<exists>\<L>. \<forall>a. output_rest_lift \<X> (\<K> a) (\<L> a) \<and> output_rest_lift \<Y> (\<L> a) (\<M> a)"
          by (fact choice)
        with that show ?thesis by blast
      qed
      then show ?case by (blast intro: output_rest_lift.with_opening_lift)
    qed
  next
    assume "(output_rest_lift \<X> OO output_rest_lift \<Y>) K M"
    then obtain L where "output_rest_lift \<X> K L" and "output_rest_lift \<Y> L M" by (elim relcomppE)
    then show "output_rest_lift (\<X> OO \<Y>) K M"
    proof (induction L arbitrary: K M rule: output_rest.induct)
      case WithoutOpening
      then show ?case
        using
          output_rest_lift.cases and
          output_rest.inject(1) and
          output_rest.distinct(2) and
          relcomppI and
          output_rest_lift.without_opening_lift
        by smt
    next
      case WithOpening
      then show ?case
        using
          output_rest_lift.cases and
          output_rest.distinct(1) and
          output_rest.inject(2) and
          rangeI and
          output_rest_lift.with_opening_lift
        by smt
    qed
  qed
qed
lemma output_rest_lift_conversion_preservation:
  "output_rest_lift \<X>\<inverse>\<inverse> = (output_rest_lift \<X>)\<inverse>\<inverse>"
proof (intro ext)
  fix K and L
  show "output_rest_lift \<X>\<inverse>\<inverse> L K \<longleftrightarrow> (output_rest_lift \<X>)\<inverse>\<inverse> L K"
  proof
    assume "output_rest_lift \<X>\<inverse>\<inverse> L K"
    then show "(output_rest_lift \<X>)\<inverse>\<inverse> L K" by induction (simp_all add: output_rest_lift.intros)
  next
    assume "(output_rest_lift \<X>)\<inverse>\<inverse> L K"
    then have "output_rest_lift \<X> K L" by (fact conversepD)
    then show "output_rest_lift \<X>\<inverse>\<inverse> L K" by induction (simp_all add: output_rest_lift.intros)
  qed
qed

text \<open>
  Consequently, \<^type>\<open>output_rest\<close> and \<^const>\<open>output_rest_lift\<close> form a residual structure.
\<close>

interpretation output_rest: residual output_rest_lift
  by unfold_locales (
    fact output_rest_lift_monotonicity,
    fact output_rest_lift_equality_preservation,
    fact output_rest_lift_composition_preservation,
    fact output_rest_lift_conversion_preservation
  )

subsection \<open>Residuals\<close>

text \<open>
  There are two kinds of residuals in the proper transition system: simple residuals, written
  \<open>\<lparr>\<delta>\<rparr> Q\<close> where \<open>\<delta>\<close> is an action, and output residuals, written
  \<open>\<lparr>c \<triangleleft> \<nu> a\<^sub>1 \<dots> a\<^sub>n. \<V> a\<^sub>1 \<dots> a\<^sub>n\<rparr> \<Q> a\<^sub>1 \<dots> a\<^sub>n\<close> where \<open>c\<close> is a channel and the \<open>a\<^sub>i\<close> are channel variables.
\<close>

datatype proper_residual =
  Simple proper_action process ("\<lparr>_\<rparr> _" [0, 51] 51) |
  Output chan output_rest ("\<lparr>_ \<triangleleft> _" [0, 51] 51)

text \<open>
  Residual lifting is defined in the obvious way.
\<close>

inductive
  proper_lift :: "(process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> (proper_residual \<Rightarrow> proper_residual \<Rightarrow> bool)"
  for \<X>
where
  simple_lift:
    "\<X> P Q \<Longrightarrow> proper_lift \<X> (\<lparr>\<alpha>\<rparr> P) (\<lparr>\<alpha>\<rparr> Q)" |
  output_lift:
    "output_rest_lift \<X> K L \<Longrightarrow> proper_lift \<X> (\<lparr>c \<triangleleft> K) (\<lparr>c \<triangleleft> L)"

text \<open>
  The \<^const>\<open>proper_lift\<close> operator has the properties of a residual lifting operator.
\<close>

lemma proper_lift_monotonicity: "\<X> \<le> \<Y> \<Longrightarrow> proper_lift \<X> \<le> proper_lift \<Y>"
proof
  fix C and D
  assume "proper_lift \<X> C D" and "\<X> \<le> \<Y>"
  then show "proper_lift \<Y> C D"
  proof induction
    case simple_lift
    then show ?case by (blast intro: proper_lift.simple_lift)
  next
    case output_lift
    then show ?case using output_rest_lift_monotonicity by (blast intro: proper_lift.output_lift)
  qed
qed
lemma proper_lift_equality_preservation: "proper_lift op = = op ="
proof (intro ext)
  fix C\<^sub>1 and C\<^sub>2
  show "proper_lift op = C\<^sub>1 C\<^sub>2 \<longleftrightarrow> C\<^sub>1 = C\<^sub>2"
  proof
    assume "proper_lift op = C\<^sub>1 C\<^sub>2"
    then show "C\<^sub>1 = C\<^sub>2"
      by induction (simp_all add: output_rest_lift_equality_preservation)
  next
    assume "C\<^sub>1 = C\<^sub>2"
    then show "proper_lift op = C\<^sub>1 C\<^sub>2" by
      (induction C\<^sub>1 arbitrary: C\<^sub>2)
      (metis output_rest_lift_equality_preservation proper_lift.intros)+
  qed
qed
lemma proper_lift_composition_preservation: "proper_lift (\<X> OO \<Y>) = proper_lift \<X> OO proper_lift \<Y>"
proof (intro ext)
  fix C and E
  show "proper_lift (\<X> OO \<Y>) C E \<longleftrightarrow> (proper_lift \<X> OO proper_lift \<Y>) C E"
  proof
    assume "proper_lift (\<X> OO \<Y>) C E"
    then show "(proper_lift \<X> OO proper_lift \<Y>) C E"
    proof induction
      case (simple_lift P R \<alpha>)
      then obtain Q where "\<X> P Q" and "\<Y> Q R" by (elim relcomppE)
      then show ?case by (blast intro: proper_lift.simple_lift)
    next
      case (output_lift K M m)
      then obtain L where "output_rest_lift \<X> K L" and "output_rest_lift \<Y> L M"
        using output_rest_lift_composition_preservation and relcomppE by metis
      then show ?case by (blast intro: proper_lift.output_lift)
    qed
  next
    assume "(proper_lift \<X> OO proper_lift \<Y>) C E"
    then obtain D where "proper_lift \<X> C D" and "proper_lift \<Y> D E" by (elim relcomppE)
    then show "proper_lift (\<X> OO \<Y>) C E"
    proof (induction D arbitrary: C E rule: proper_residual.induct)
      case Simple
      then show ?case
        using
          proper_lift.cases and
          proper_residual.inject(1) and
          proper_residual.distinct(2) and
          relcomppI and
          proper_lift.simple_lift
        by smt
    next
      case Output
      then show ?case
        using
          proper_lift.cases and
          proper_residual.distinct(1) and
          proper_residual.inject(2) and
          relcomppI and
          output_rest_lift_composition_preservation and
          proper_lift.output_lift
        by smt
    qed
  qed
qed
lemma proper_lift_conversion_preservation: "proper_lift \<X>\<inverse>\<inverse> = (proper_lift \<X>)\<inverse>\<inverse>"
proof (intro ext)
  fix C and D
  show "proper_lift \<X>\<inverse>\<inverse> D C \<longleftrightarrow> (proper_lift \<X>)\<inverse>\<inverse> D C"
  proof
    assume "proper_lift \<X>\<inverse>\<inverse> D C"
    then show "(proper_lift \<X>)\<inverse>\<inverse> D C"
      by induction (simp_all add: output_rest_lift_conversion_preservation proper_lift.intros)
  next
    assume "(proper_lift \<X>)\<inverse>\<inverse> D C"
    then have "proper_lift \<X> C D" by (fact conversepD)
    then show "proper_lift \<X>\<inverse>\<inverse> D C"
      by induction (metis conversepI output_rest_lift_conversion_preservation proper_lift.intros)+
  qed
qed

text \<open>
  Consequently, \<^type>\<open>proper_residual\<close> and \<^const>\<open>proper_lift\<close> form a residual structure.
\<close>

interpretation proper: residual proper_lift
  by unfold_locales (
    fact proper_lift_monotonicity,
    fact proper_lift_equality_preservation,
    fact proper_lift_composition_preservation,
    fact proper_lift_conversion_preservation
  )

subsection \<open>Transition System\<close>

text \<open>
  The following definition of the transition relation captures the set of rules that define the
  transition system.
\<close>

inductive
  proper_transition :: "process \<Rightarrow> proper_residual \<Rightarrow> bool"
  (infix "\<longmapsto>\<^sub>\<sharp>" 50)
where
  simple:
    "P \<longmapsto>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> Q \<Longrightarrow> P \<longmapsto>\<^sub>\<sharp>\<lparr>\<delta>\<rparr> Q" |
  output_without_opening:
    "P \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleleft> V\<rbrace> Q \<Longrightarrow> P \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> V\<rparr> Q" |
  output_with_opening:
    "\<lbrakk> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Q> a \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<K> a \<rbrakk> \<Longrightarrow> P \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<nu> a. \<K> a"

text \<open>
  The residual structure and \<^const>\<open>proper_transition\<close> together form a transition system.
\<close>

interpretation proper: transition_system proper_lift proper_transition
  by unfold_locales

text \<open>
  We introduce concise notation for some of the derived predicates of the transition system.
\<close>

abbreviation
  proper_sim :: "(process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> bool"
  ("sim\<^sub>\<sharp>")
where
  "sim\<^sub>\<sharp> \<equiv> proper.sim"
abbreviation
  proper_bisim :: "(process \<Rightarrow> process \<Rightarrow> bool) \<Rightarrow> bool"
  ("bisim\<^sub>\<sharp>")
where
  "bisim\<^sub>\<sharp> \<equiv> proper.bisim"
abbreviation
  proper_pre_bisimilarity :: "process \<Rightarrow> process \<Rightarrow> bool"
  (infix "\<preceq>\<^sub>\<sharp>" 50)
where
  "op \<preceq>\<^sub>\<sharp> \<equiv> proper.pre_bisimilarity"
abbreviation
  proper_bisimilarity :: "process \<Rightarrow> process \<Rightarrow> bool"
  (infix "\<sim>\<^sub>\<sharp>" 50)
where
  "op \<sim>\<^sub>\<sharp> \<equiv> proper.bisimilarity"

subsection \<open>Fundamental Properties of the Transition System\<close>

lemma no_proper_transitions_from_stop: "\<not> \<zero> \<longmapsto>\<^sub>\<sharp>C"
proof
  fix C
  assume "\<zero> \<longmapsto>\<^sub>\<sharp>C"
  then show False
    by (induction "\<zero>" C) (simp_all add: no_basic_transitions_from_stop)
qed

subsection \<open>Relationships between Basic and Proper Bisimilarity\<close>

lemma basic_bisimilarity_is_proper_simulation: "sim\<^sub>\<sharp> op \<sim>\<^sub>\<flat>"
proof (intro predicate2I, intro allI, intro impI)
  fix P and Q and C
  assume "P \<longmapsto>\<^sub>\<sharp>C" and "P \<sim>\<^sub>\<flat> Q"
  then show "\<exists>D. Q \<longmapsto>\<^sub>\<sharp>D \<and> proper_lift op \<sim>\<^sub>\<flat> C D"
  proof (induction arbitrary: Q)
    case (simple P \<delta> P' Q)
    from `P \<sim>\<^sub>\<flat> Q` and `P \<longmapsto>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> P'`
    obtain Q' where "Q \<longmapsto>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> Q'" and "P' \<sim>\<^sub>\<flat> Q'"
      using
        basic.bisimilarity_is_simulation and
        predicate2D and
        basic_lift.cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then show ?case
      by (blast intro: proper_transition.simple simple_lift)
  next
    case (output_without_opening P c V P' Q)
    from `P \<sim>\<^sub>\<flat> Q` and `P \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleleft> V\<rbrace> P'`
    obtain Q' where "Q \<longmapsto>\<^sub>\<flat>\<lbrace>c \<triangleleft> V\<rbrace> Q'" and "P' \<sim>\<^sub>\<flat> Q'"
      using
        basic.bisimilarity_is_simulation and
        predicate2D and
        basic_lift.cases and
        basic_residual.inject(1) and
        basic_residual.distinct(2)
      by smt
    then show ?case
      by (blast intro: proper_transition.output_without_opening without_opening_lift output_lift)
  next
    case (output_with_opening P \<P> c \<K> Q)
    obtain \<Q> where "Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a" and "\<And>a. \<P> a \<sim>\<^sub>\<flat> \<Q> a"
    proof -
      from `P \<sim>\<^sub>\<flat> Q` and `P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a`
      obtain D where "Q \<longmapsto>\<^sub>\<flat>D" and "basic_lift op \<sim>\<^sub>\<flat> (\<lbrace>\<nu> a\<rbrace> \<P> a) D"
        using basic.bisimilarity_is_simulation
        by blast
      from `basic_lift op \<sim>\<^sub>\<flat> (\<lbrace>\<nu> a\<rbrace> \<P> a) D` and `Q \<longmapsto>\<^sub>\<flat>D` and that show ?thesis
        by cases simp
    qed
    (*
      In case we provide lemmas or proof methods for statements that we currently solve with smt,
      note that the above statement was formerly also proved using smt (after the dropping of
      contexts this surprisingly did not work anymore). Here is the old code:

          from `P \<sim>\<^sub>\<flat> Q` and `P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a`
          obtain \<Q> where "Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a" and "\<And>a. \<P> a \<sim>\<^sub>\<flat> \<Q> a"
            using
              basic.bisimilarity_is_simulation and
              predicate2D and
              basic_lift.cases and
              basic_residual.distinct(1) and
              basic_residual.inject(2)
            by smt
    *)
    obtain \<L> where "\<And>a. \<Q> a \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<L> a" and "\<And>a. output_rest_lift op \<sim>\<^sub>\<flat> (\<K> a) (\<L> a)"
    proof -
      from output_with_opening.IH and `\<And>a. \<P> a \<sim>\<^sub>\<flat> \<Q> a`
      have "\<forall>a. \<exists>L. \<Q> a \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> L \<and> output_rest_lift op \<sim>\<^sub>\<flat> (\<K> a) L"
        using
          proper_lift.cases and
          proper_residual.distinct(1) and
          proper_residual.inject(2)
        by smt
      then have "\<exists>\<L>. \<forall>a. \<Q> a \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<L> a \<and> output_rest_lift op \<sim>\<^sub>\<flat> (\<K> a) (\<L> a)"
        by (fact choice)
      with that show ?thesis by blast
    qed
    from `Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a` and `\<And>a. \<Q> a \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<L> a` have "Q \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<nu> a. \<L> a"
      by (fact proper_transition.output_with_opening)
    with `\<And>a. output_rest_lift op \<sim>\<^sub>\<flat> (\<K> a) (\<L> a)` show ?case
      using with_opening_lift and output_lift
      by smt
  qed
qed

lemma basic_bisimilarity_is_proper_bisimulation: "bisim\<^sub>\<sharp> op \<sim>\<^sub>\<flat>"
  using basic.bisimilarity_symmetry and basic_bisimilarity_is_proper_simulation
  by (fact proper.symmetric_simulation_is_bisimulation)

lemma basic_bisimilarity_in_proper_bisimilarity: "op \<sim>\<^sub>\<flat> \<le> op \<sim>\<^sub>\<sharp>"
  using basic_bisimilarity_is_proper_bisimulation
  by (fact proper.bisimulation_in_bisimilarity)

lemma basic_bisimilarity_in_proper_bisimilarity_rule: "P \<sim>\<^sub>\<flat> Q \<Longrightarrow> P \<sim>\<^sub>\<sharp> Q"
  using basic_bisimilarity_in_proper_bisimilarity ..

subsection \<open>Concrete Bisimilarities\<close>

lemma proper_receive_preservation: "(\<And>x. \<P> x \<sim>\<^sub>\<sharp> \<Q> x) \<Longrightarrow> c \<triangleright> x. \<P> x \<sim>\<^sub>\<sharp> c \<triangleright> x. \<Q> x"
  sorry

lemma proper_parallel_preservation: "P \<sim>\<^sub>\<sharp> Q \<Longrightarrow> P \<parallel> R \<sim>\<^sub>\<sharp> Q \<parallel> R"
  sorry

lemma proper_new_channel_preservation: "(\<And>a. \<P> a \<sim>\<^sub>\<sharp> \<Q> a) \<Longrightarrow> \<nu> a. \<P> a \<sim>\<^sub>\<sharp> \<nu> a. \<Q> a"
  sorry

context begin

private lemma proper_pre_receive_scope_extension_ltr: "c \<triangleright> x. \<nu> a. \<P> x a \<preceq>\<^sub>\<sharp> \<nu> a. c \<triangleright> x. \<P> x a"
proof (standard, intro allI, intro impI)
  fix C
  assume "c \<triangleright> x. \<nu> a. \<P> x a \<longmapsto>\<^sub>\<sharp>C"
  then show "\<exists>D. \<nu> a. c \<triangleright> x. \<P> x a \<longmapsto>\<^sub>\<sharp>D \<and> proper_lift op \<sim>\<^sub>\<sharp> C D"
  proof cases
    case (simple \<delta> Q)
    from `c \<triangleright> x. \<nu> a. \<P> x a \<longmapsto>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> Q`
    obtain V where "basic_action_of \<delta> = c \<triangleright> V" and "Q = \<nu> a. \<P> V a"
      by (blast elim: basic_transitions_from_receive)
    from `basic_action_of \<delta> = c \<triangleright> V` have "\<nu> a. c \<triangleright> x. \<P> x a \<longmapsto>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<nu> a. \<P> V a"
      using receiving and acting_scope
      by smt
    with `C = \<lparr>\<delta>\<rparr> Q` and `Q = \<nu> a. \<P> V a` have "\<nu> a. c \<triangleright> x. \<P> x a \<longmapsto>\<^sub>\<sharp>C"
      by (blast intro: proper_transition.simple)
    then show ?thesis
      using proper.bisimilarity_reflexivity and proper.lift_reflexivity_propagation and reflpD
      by smt
  next
    case (output_without_opening c V Q)
    then show ?thesis
      using basic_transitions_from_receive
      by fastforce
  next
    case output_with_opening
    then show ?thesis by (simp add: no_opening_transitions_from_receive)
  qed
qed

private lemma opening_transitions_from_new_channel_receive:
  "\<nu> a. c \<triangleright> x. \<P> x a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<Q> a = c \<triangleright> x . \<P> x a"
proof (induction "\<nu> a. c \<triangleright> x. \<P> x a" "\<lbrace>\<nu> a\<rbrace> \<Q> a" arbitrary: \<Q> rule: basic_transition.induct)
  case opening
  show ?case by (fact refl)
next
  case scoped_opening
  then show ?case using no_opening_transitions_from_receive by metis
qed

private lemma proper_pre_receive_scope_extension_rtl: "\<nu> a. c \<triangleright> x. \<P> x a \<preceq>\<^sub>\<sharp> c \<triangleright> x. \<nu> a. \<P> x a"
proof (standard, intro allI, intro impI)
  fix C
  assume "\<nu> a. c \<triangleright> x. \<P> x a \<longmapsto>\<^sub>\<sharp>C"
  then show "\<exists>D. c \<triangleright> x. \<nu> a. \<P> x a \<longmapsto>\<^sub>\<sharp>D \<and> proper_lift op \<sim>\<^sub>\<sharp> C D"
  proof cases
    case (simple \<delta> R)
    from `\<nu> a. c \<triangleright> x. \<P> x a \<longmapsto>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> R` show ?thesis
    proof cases
      case (scoped_acting \<Q> \<R>)
      from `\<nu> a. c \<triangleright> x. \<P> x a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a` have "\<And>a. \<Q> a = c \<triangleright> x . \<P> x a"
        by (fact opening_transitions_from_new_channel_receive)
      with `\<And>a. \<Q> a \<longmapsto>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<R> a`
      obtain V where "basic_action_of \<delta> = c \<triangleright> V" and "\<And>a. \<R> a = \<P> V a"
        using
          basic_transitions_from_receive and
          basic_residual.inject(1) and
          basic_action.inject(1) and
          io_action.inject(1)
        by smt
      from `basic_action_of \<delta> = c \<triangleright> V` have "c \<triangleright> x. \<nu> a. \<P> x a \<longmapsto>\<^sub>\<flat>\<lbrace>basic_action_of \<delta>\<rbrace> \<nu> a. \<P> V a"
        using receiving
        by fastforce
      moreover from `C = \<lparr>\<delta>\<rparr> R` and `R = \<nu> a. \<R> a` and `\<And>a. \<R> a = \<P> V a` have "C = \<lparr>\<delta>\<rparr> \<nu> a. \<P> V a"
        by simp
      ultimately have "c \<triangleright> x. \<nu> a. \<P> x a \<longmapsto>\<^sub>\<sharp>C"
        by (blast intro: proper_transition.simple)
      then show ?thesis
        using proper.bisimilarity_reflexivity and proper.lift_reflexivity_propagation and reflpD
        by smt
    qed
  next
    case (output_without_opening c' V R)
    from `\<nu> a. c \<triangleright> x. \<P> x a \<longmapsto>\<^sub>\<flat>\<lbrace>c' \<triangleleft> V\<rbrace> R` show ?thesis
    proof cases
      case (scoped_acting \<Q> \<R>)
      from `\<nu> a. c \<triangleright> x. \<P> x a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a` have "\<And>a. \<Q> a = c \<triangleright> x. \<P> x a"
        by (fact opening_transitions_from_new_channel_receive)
      with `\<And>a. \<Q> a \<longmapsto>\<^sub>\<flat>\<lbrace>c' \<triangleleft> V\<rbrace> \<R> a` show ?thesis
        using basic_transitions_from_receive and basic_residual.inject(1)
        by fastforce
    qed
  next
    case (output_with_opening \<Q> c' \<K>)
    from `\<nu> a. c \<triangleright> x. \<P> x a \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a` have "\<And>a. \<Q> a = c \<triangleright> x. \<P> x a"
      by (fact opening_transitions_from_new_channel_receive)
    with `\<And>a. \<Q> a \<longmapsto>\<^sub>\<sharp>\<lparr>c' \<triangleleft> \<K> a` have "c \<triangleright> x. \<P> x undefined \<longmapsto>\<^sub>\<sharp>\<lparr>c' \<triangleleft> \<K> undefined"
      by simp
    then show ?thesis
    proof cases
      case (output_without_opening V Q)
      then show ?thesis
        using basic_transitions_from_receive
        by fastforce
    next
      case output_with_opening
      then show ?thesis by (simp add: no_opening_transitions_from_receive)
    qed
  qed
qed

lemma proper_receive_scope_extension: "c \<triangleright> x. \<nu> a. \<P> x a \<sim>\<^sub>\<sharp> \<nu> a. c \<triangleright> x. \<P> x a"
  by standard (
    fact proper_pre_receive_scope_extension_ltr,
    fact proper_pre_receive_scope_extension_rtl
  )

end

lemma proper_parallel_scope_extension: "\<nu> a. \<P> a \<parallel> Q \<sim>\<^sub>\<sharp> \<nu> a. (\<P> a \<parallel> Q)"
  using basic_parallel_scope_extension
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

lemma proper_new_channel_scope_extension: "\<nu> b. \<nu> a. \<P> a b \<sim>\<^sub>\<sharp> \<nu> a. \<nu> b. \<P> a b"
  using basic_new_channel_scope_extension
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

lemma proper_parallel_unit: "\<zero> \<parallel> P \<sim>\<^sub>\<sharp> P"
  using basic_parallel_unit
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

lemma proper_parallel_commutativity: "P \<parallel> Q \<sim>\<^sub>\<sharp> Q \<parallel> P"
  using basic_parallel_commutativity
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

lemma proper_parallel_associativity: "(P \<parallel> Q) \<parallel> R \<sim>\<^sub>\<sharp> P \<parallel> (Q \<parallel> R)"
  using basic_parallel_associativity
  by (intro basic_bisimilarity_in_proper_bisimilarity_rule)

context begin

private lemma opening_transitions_from_new_channel_stop: "\<nu> a. \<zero> \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<Longrightarrow> \<P> a = \<zero>"
proof -
  fix \<P> and a
  assume "\<nu> a. \<zero> \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a"
  then show "\<P> a = \<zero>"
  proof (induction "\<nu> a. \<zero>" "\<lbrace>\<nu> a\<rbrace> \<P> a" arbitrary: \<P>)
    case opening
    show ?case by (fact refl)
  next
    case scoped_opening
    then show ?case using no_basic_transitions_from_stop by metis
  qed
qed

private lemma no_acting_transitions_from_new_channel_stop: "\<not> \<nu> a. \<zero> \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P"
proof
  fix \<alpha> and P
  assume "\<nu> a. \<zero> \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P"
  then show False
  proof cases
    case (scoped_acting \<Q>\<^sub>1 \<Q>\<^sub>2)
    from `\<nu> a. \<zero> \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q>\<^sub>1 a` have "\<And>a. \<Q>\<^sub>1 a = \<zero>"
      by (fact opening_transitions_from_new_channel_stop)
    with `\<And>a. \<Q>\<^sub>1 a \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<Q>\<^sub>2 a` show ?thesis
      by (simp add: no_basic_transitions_from_stop)
  qed
qed

private lemma no_proper_transitions_from_new_channel_stop: "\<not> \<nu> a. \<zero> \<longmapsto>\<^sub>\<sharp>C"
proof
  fix C
  assume "\<nu> a. \<zero> \<longmapsto>\<^sub>\<sharp>C"
  then show False
  proof cases
    case (output_with_opening \<P> c \<K>)
    from `\<nu> a. \<zero> \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a` have "\<And>a. \<P> a = \<zero>"
      by (fact opening_transitions_from_new_channel_stop)
    with `\<And>a. \<P> a \<longmapsto>\<^sub>\<sharp>\<lparr>c \<triangleleft> \<K> a` show ?thesis
      by (simp add: no_proper_transitions_from_stop)
  qed (simp_all add: no_acting_transitions_from_new_channel_stop)
qed

private lemma proper_stop_scope_redundancy: "\<zero> \<sim>\<^sub>\<sharp> \<nu> a. \<zero>"
proof
  show "\<zero> \<preceq>\<^sub>\<sharp> \<nu> a. \<zero>"
    using no_proper_transitions_from_stop
    by (blast intro: proper.pre_bisimilarity.intros)
next
  show "\<nu> a. \<zero> \<preceq>\<^sub>\<sharp> \<zero>"
    using no_proper_transitions_from_new_channel_stop
    by (blast intro: proper.pre_bisimilarity.intros)
qed

lemma proper_scope_redundancy: "P \<sim>\<^sub>\<sharp> \<nu> a. P"
proof -
  have "P \<sim>\<^sub>\<sharp> \<zero> \<parallel> P"
    by (rule proper.bisimilarity_symmetry_rule) (fact proper_parallel_unit)
  also have "\<zero> \<parallel> P \<sim>\<^sub>\<sharp> \<nu> a. \<zero> \<parallel> P"
    using proper_stop_scope_redundancy and proper_parallel_preservation by blast
  also have "\<nu> a. \<zero> \<parallel> P \<sim>\<^sub>\<sharp> \<nu> a. (\<zero> \<parallel> P)"
    by (fact proper_parallel_scope_extension)
  also have "\<nu> a. (\<zero> \<parallel> P) \<sim>\<^sub>\<sharp> \<nu> a. P"
    using proper_parallel_unit and proper_new_channel_preservation by metis
  finally show ?thesis .
qed

end

subsection \<open>Conclusion\<close>

text \<open>
  This is all for the proper transition system.
\<close>

end
