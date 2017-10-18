
theory KMP
  imports Refine_Imperative_HOL.IICF
    "HOL-Library.Sublist"
    "HOL-Library.Code_Char"
begin

text\<open>Test. @{cite "Refine_Imperative_HOL-AFP"} Working? Test 2 @{cite FPMIS} @{cite GAD}\<close>

declare len_greater_imp_nonempty[simp del] min_absorb2[simp]
no_notation Ref.update ("_ := _" 62)

section\<open>Specification\<close>

subsection\<open>Sublist-predicate with a position check\<close>

subsubsection\<open>Definition\<close>

text \<open>One could define\<close>
definition "sublist_at' xs ys i \<equiv> take (length xs) (drop i ys) = xs"  

text\<open>However, this doesn't handle out-of-bound indexes uniformly:\<close>
value[nbe] "sublist_at' [] [a] 5"
value[nbe] "sublist_at' [a] [a] 5"
value[nbe] "sublist_at' [] [] 5"

text\<open>Instead, we use a recursive definition:\<close>
fun sublist_at :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "sublist_at (x#xs) (y#ys) 0 \<longleftrightarrow> x=y \<and> sublist_at xs ys 0" |
  "sublist_at xs (y#ys) (Suc i) \<longleftrightarrow> sublist_at xs ys i" |
  "sublist_at [] ys 0 \<longleftrightarrow> True" |
  "sublist_at _ [] _ \<longleftrightarrow> False"

text\<open>In the relevant cases, both definitions agree:\<close>
lemma "i \<le> length ys \<Longrightarrow> sublist_at xs ys i \<longleftrightarrow> sublist_at' xs ys i"
  unfolding sublist_at'_def
  by (induction xs ys i rule: sublist_at.induct) auto

text\<open>However, the new definition has some reasonable properties:\<close>
subsubsection\<open>Properties\<close>
lemma sublist_lengths: "sublist_at xs ys i \<Longrightarrow> i + length xs \<le> length ys"
  by (induction xs ys i rule: sublist_at.induct) auto

lemma Nil_is_sublist: "sublist_at ([] :: 'x list) ys i \<longleftrightarrow> i \<le> length ys"
  by (induction "[] :: 'x list" ys i rule: sublist_at.induct) auto

text\<open>Furthermore, we need:\<close>
lemma sublist_step[intro]:
  "\<lbrakk>i + length xs < length ys; sublist_at xs ys i; ys!(i + length xs) = x\<rbrakk> \<Longrightarrow> sublist_at (xs@[x]) ys i"
  apply (induction xs ys i rule: sublist_at.induct)
  apply auto
  using sublist_at.elims(3) by fastforce

lemma all_positions_sublist:
"\<lbrakk>i + length xs \<le> length ys; \<forall>jj<length xs. ys!(i+jj) = xs!jj\<rbrakk> \<Longrightarrow> sublist_at xs ys i"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by (simp add: Nil_is_sublist)
next
  case (snoc x xs)
  from \<open>i + length (xs @ [x]) \<le> length ys\<close> have "i + length xs \<le> length ys" by simp
  moreover have "\<forall>jj<length xs. ys!(i + jj) = xs!jj"
    by (simp add: nth_append snoc.prems(2))
  ultimately have "sublist_at xs ys i"
    using snoc.IH by simp
  then show ?case
    using snoc.prems by auto
qed

lemma sublist_all_positions: "sublist_at xs ys i \<Longrightarrow> \<forall>jj<length xs. ys!(i+jj) = xs!jj"
  by (induction xs ys i rule: sublist_at.induct) (auto simp: nth_Cons')

text\<open>It also connects well to theory @{theory Sublist} (compare @{thm[source] sublist_def}):\<close>
lemma sublist_at_altdef:
  "sublist_at xs ys i \<longleftrightarrow> (\<exists>ps ss. ys = ps@xs@ss \<and> i = length ps)"
proof (induction xs ys i rule: sublist_at.induct)
  case (2 ss t ts i)
  show "sublist_at ss (t#ts) (Suc i) \<longleftrightarrow> (\<exists>xs ys. t#ts = xs@ss@ys \<and> Suc i = length xs)"
    (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs
    then have "sublist_at ss ts i" by simp
    with "2.IH" obtain xs where "\<exists>ys. ts = xs@ss@ys \<and> i = length xs" by auto
    then have "\<exists>ys. t#ts = (t#xs)@ss@ys \<and> Suc i = length (t#xs)" by simp
    then show ?rhs by blast
  next
    assume ?rhs
    then obtain xs where "\<exists>ys. t#ts = xs@ss@ys \<and> Suc i = length xs" by blast
    then have "\<exists>ys. ts = (tl xs)@ss@ys \<and> i = length (tl xs)"
      by (metis hd_Cons_tl length_0_conv list.sel(3) nat.simps(3) size_Cons_lem_eq tl_append2)
    then have "\<exists>xs ys. ts = xs@ss@ys \<and> i = length xs" by blast
    with "2.IH" show ?lhs by simp
  qed
qed auto

corollary sublist_iff_sublist_at: "Sublist.sublist xs ys \<longleftrightarrow> (\<exists>i. sublist_at xs ys i)"
  by (simp add: sublist_at_altdef Sublist.sublist_def)

subsection\<open>Sublist-check algorithms\<close>

text\<open>@{term s} for "searchword" / "searchlist", @{term t} for "text"\<close>
definition "kmp_SPEC s t = SPEC (\<lambda>
  None \<Rightarrow> \<nexists>i. sublist_at s t i |
  Some i \<Rightarrow> sublist_at s t i \<and> (\<forall>ii<i. \<not>sublist_at s t ii))"

lemma is_arg_min_id: "is_arg_min id P i \<longleftrightarrow> P i \<and> (\<forall>ii<i. \<not>P ii)"
  unfolding is_arg_min_def by auto

lemma kmp_result: "kmp_SPEC s t =
  RETURN (if sublist s t then Some (LEAST i. sublist_at s t i) else None)"
  unfolding kmp_SPEC_def sublist_iff_sublist_at
  apply (auto intro: LeastI dest: not_less_Least split: option.splits)
  by (meson LeastI nat_neq_iff not_less_Least)

corollary weak_kmp_SPEC: "kmp_SPEC s t \<le> SPEC (\<lambda>pos. pos\<noteq>None \<longleftrightarrow> Sublist.sublist s t)"
  by (simp add: kmp_result)

lemmas kmp_SPEC_altdefs =
  kmp_SPEC_def[folded is_arg_min_id]
  kmp_SPEC_def[folded sublist_iff_sublist_at]
  kmp_result

section\<open>Naive algorithm\<close>

text\<open>Since KMP is a direct advancement of the naive "test-all-starting-positions" approach, we provide it here for comparison:\<close>

subsection\<open>Invariants\<close>
definition "I_out_na s t \<equiv> \<lambda>(i,j,pos).
  (\<forall>ii<i. \<not>sublist_at s t ii) \<and>
  (case pos of None \<Rightarrow> j = 0
    | Some p \<Rightarrow> p=i \<and> sublist_at s t i)"
definition "I_in_na s t i \<equiv> \<lambda>(j,pos).
  case pos of None \<Rightarrow> j < length s \<and> (\<forall>jj<j. t!(i+jj) = s!(jj))
    | Some p \<Rightarrow> sublist_at s t i"

subsection\<open>Algorithm\<close>

(*Algorithm is common knowledge \<longrightarrow> remove citation here?*)
text\<open>The following definition is taken from Helmut Seidl's lecture on algorithms and data structures@{cite GAD} except that we
\<^item> output the identified position @{term \<open>pos :: nat option\<close>} instead of just @{const True}
\<^item> use @{term \<open>pos :: nat option\<close>} as break-flag to support the abort within the loops
\<^item> rewrite @{prop \<open>i \<le> length t - length s\<close>} in the first while-condition to @{prop \<open>i + length s \<le> length t\<close>} to avoid having to use @{type int} for list indexes (or the additional precondition @{prop \<open>length s \<le> length t\<close>})
\<close>

definition "naive_algorithm s t \<equiv> do {
  let i=0;
  let j=0;
  let pos=None;
  (_,_,pos) \<leftarrow> WHILEIT (I_out_na s t) (\<lambda>(i,_,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    (_,pos) \<leftarrow> WHILEIT (I_in_na s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,_). do {
      let j=j+1;
      if j=length s then RETURN (j,Some i) else RETURN (j,None)
    }) (j,pos);
    if pos=None then do {
      let i = i + 1;
      let j = 0;
      RETURN (i,j,None)
    } else RETURN (i,j,Some i)
  }) (i,j,pos);

  RETURN pos
}"

subsection\<open>Correctness\<close>

text\<open>The basic lemmas on @{const sublist_at} from the previous chapter together with @{theory Refine_Monadic}'s verification condition generator / solver suffice:\<close>

lemma "s \<noteq> [] \<Longrightarrow> naive_algorithm s t \<le> kmp_SPEC s t"
  unfolding naive_algorithm_def kmp_SPEC_def I_out_na_def I_in_na_def
  apply (refine_vcg
    WHILEIT_rule[where R="measure (\<lambda>(i,_,pos). length t - i + (if pos = None then 1 else 0))"]
    WHILEIT_rule[where R="measure (\<lambda>(j,_::nat option). length s - j)"]
    )
  apply (vc_solve solve: asm_rl)
  subgoal by (metis add_Suc_right all_positions_sublist less_antisym)
  subgoal using less_Suc_eq by blast
  subgoal by (metis less_SucE sublist_all_positions)
  subgoal by (auto split: option.splits) (metis sublist_lengths add_less_cancel_right leI le_less_trans)
  done

text\<open>Note that the precondition cannot be removed without an extra branch: If @{prop \<open>s = []\<close>}, the inner while-condition accesses out-of-bound memory. This will apply to KMP, too.\<close>

section\<open>Knuth–Morris–Pratt algorithm\<close>
subsection\<open>Borders of lists\<close>

definition "border xs ys \<longleftrightarrow> prefix xs ys \<and> suffix xs ys"
definition "strict_border xs ys \<longleftrightarrow> border xs ys \<and> length xs < length ys"
definition "intrinsic_border ls \<equiv> ARG_MAX length b. strict_border b ls"

subsubsection\<open>Properties\<close>

interpretation border_order: order border strict_border
  by standard (auto simp: border_def suffix_def strict_border_def)
interpretation border_bot: order_bot Nil border strict_border
  by standard (simp add: border_def)

lemma borderE[elim]:
  fixes xs ys :: "'a list"
  assumes "border xs ys"
  obtains "prefix xs ys" and "suffix xs ys"
  using assms unfolding border_def by blast

lemma strict_borderE[elim]:
  fixes xs ys :: "'a list"
  assumes "strict_border xs ys"
  obtains "border xs ys" and "length xs < length ys"
  using assms unfolding strict_border_def by blast

lemma strict_border_simps[simp]:
  "strict_border xs [] \<longleftrightarrow> False"
  "strict_border [] (x # xs) \<longleftrightarrow> True"
  by (simp_all add: strict_border_def)

lemma strict_border_prefix: "strict_border xs ys \<Longrightarrow> strict_prefix xs ys"
  and strict_border_suffix: "strict_border xs ys \<Longrightarrow> strict_suffix xs ys"
  and strict_border_imp_nonempty: "strict_border xs ys \<Longrightarrow> ys \<noteq> []"
  and strict_border_prefix_suffix: "strict_border xs ys \<longleftrightarrow> strict_prefix xs ys \<and> strict_suffix xs ys"
  by (auto simp: border_order.order.strict_iff_order border_def)

lemma border_length_le: "border xs ys \<Longrightarrow> length xs \<le> length ys"
  unfolding border_def by (simp add: prefix_length_le)

lemma border_length_r_less (*rm*): "\<forall>xs. strict_border xs ys \<longrightarrow> length xs < length ys"
  using strict_borderE by auto

lemma border_positions: "border xs ys \<Longrightarrow> \<forall>i<length xs. ys!i = ys!(length ys - length xs + i)"
  unfolding border_def
  by (metis diff_add_inverse diff_add_inverse2 length_append not_add_less1 nth_append prefixE suffixE)

(*Todo: swap names, add i+\<dots>, decide whether w instead of x and w is enough*)
lemma all_positions_drop_length_take: "\<lbrakk>i \<le> length w; i \<le> length x;
  \<forall>j<i. x ! j = w ! (length w + j - i)\<rbrakk>
    \<Longrightarrow> drop (length w - i) w = take i x"
  by (cases "i = length x") (simp_all add: nth_equalityI)

lemma all_positions_suffix_take: "\<lbrakk>i \<le> length w; i \<le> length x;
  \<forall>j<i. x ! j = w ! (length w + j - i)\<rbrakk>
    \<Longrightarrow> suffix (take i x) w"
  by (metis all_positions_drop_length_take suffix_drop)

lemma suffix_butlast: "suffix xs ys \<Longrightarrow> suffix (butlast xs) (butlast ys)"
  unfolding suffix_def by (metis append_Nil2 butlast.simps(1) butlast_append)

lemma positions_border: "\<forall>j<l. w!j = w!(length w - l + j) \<Longrightarrow> border (take l w) w"
  by (cases "l < length w") (simp_all add: border_def all_positions_suffix_take take_is_prefix)

lemma positions_strict_border: "l < length w \<Longrightarrow> \<forall>j<l. w!j = w!(length w - l + j) \<Longrightarrow> strict_border (take l w) w"
  by (simp add: positions_border strict_border_def)

lemma "needed?": "w \<noteq> [] \<Longrightarrow> strict_border (intrinsic_border w) w"
  (*equivalent to intrinsic_borderI'*)
  unfolding intrinsic_border_def
  thm arg_max_natI[of _ "[]"]
  apply (rule arg_max_natI[of _ "[]"])
   apply (simp add: border_bot.bot.not_eq_extremum)
  using strict_borderE by auto

lemmas intrinsic_borderI = arg_max_natI[OF _ border_length_r_less, folded intrinsic_border_def]

lemmas intrinsic_borderI' = border_bot.bot.not_eq_extremum[THEN iffD1, THEN intrinsic_borderI]

lemmas intrinsic_border_max = arg_max_nat_le[OF _ border_length_r_less, folded intrinsic_border_def]

lemma nonempty_is_arg_max_ib: "ys \<noteq> [] \<Longrightarrow> is_arg_max length (\<lambda>xs. strict_border xs ys) (intrinsic_border ys)"
  by (simp add: intrinsic_borderI' intrinsic_border_max is_arg_max_linorder)

lemma intrinsic_border_less: "w \<noteq> [] \<Longrightarrow> length (intrinsic_border w) < length w"
  using intrinsic_borderI[of w] border_length_r_less "needed?" by blast

lemma intrinsic_border_less': "j > 0 \<Longrightarrow> w \<noteq> [] \<Longrightarrow> length (intrinsic_border (take j w)) < length w"
  by (metis intrinsic_border_less length_take less_not_refl2 min_less_iff_conj take_eq_Nil)

subsubsection\<open>Examples\<close>

lemma border_example: "{b. border b ''aabaabaa''} = {'''', ''a'', ''aa'', ''aabaa'', ''aabaabaa''}"
  (is "{b. border b ?l} = {?take0, ?take1, ?take2, ?take5, ?l}")
proof
  show "{?take0, ?take1, ?take2, ?take5, ?l} \<subseteq> {b. border b ?l}"
    by simp eval
  have "\<not>border ''aab'' ?l" "\<not>border ''aaba'' ?l" "\<not>border ''aabaab'' ?l" "\<not>border ''aabaaba'' ?l"
    by eval+
  moreover have "{b. border b ?l} \<subseteq> set (prefixes ?l)"
    using border_def in_set_prefixes by blast
  ultimately show "{b. border b ?l} \<subseteq> {?take0, ?take1, ?take2, ?take5, ?l}"
    by auto
qed

corollary strict_border_example: "{b. strict_border b ''aabaabaa''} = {'''', ''a'', ''aa'', ''aabaa''}"
  (is "?l = ?r")
proof
  have "?l \<subseteq> {b. border b ''aabaabaa''}"
    by auto
  also have "\<dots> = {'''', ''a'', ''aa'', ''aabaa'', ''aabaabaa''}"
    by (fact border_example)
  finally show "?l \<subseteq> ?r" by auto
  show "?r \<subseteq> ?l" by simp eval
qed

corollary "intrinsic_border ''aabaabaa'' = ''aabaa''"
proof - \<comment>\<open>We later obtain a fast algorithm for that.\<close>
  have exhaust: "strict_border b ''aabaabaa'' \<longleftrightarrow> b \<in> {[], ''a'', ''aa'', ''aabaa''}" for b
    using strict_border_example by auto
  then have
    "\<not>is_arg_max length (\<lambda>b. strict_border b ''aabaabaa'') ''''"
    "\<not>is_arg_max length (\<lambda>b. strict_border b ''aabaabaa'') ''a''"
    "\<not>is_arg_max length (\<lambda>b. strict_border b ''aabaabaa'') ''aa''"
    "is_arg_max length (\<lambda>b. strict_border b ''aabaabaa'') ''aabaa''"
    unfolding is_arg_max_linorder by auto
  moreover have "strict_border (intrinsic_border ''aabaabaa'') ''aabaabaa''"
    using intrinsic_borderI' by blast
  note this[unfolded exhaust]
  ultimately show ?thesis
    by simp (metis list.discI nonempty_is_arg_max_ib)
qed

subsection\<open>Main routine\<close>

text\<open>"Intrinsic border length plus one" for prefixes\<close>
fun iblp1 :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "iblp1 s 0 = 0" \<comment>\<open>This increments the compare position while @{prop \<open>j=(0::nat)\<close>}\<close> |
  "iblp1 s j = length (intrinsic_border (take j s)) + 1"
  --\<open>Todo: Better name, use @{command definition} and @{const If} instead of fake pattern matching, then prove @{attribute simp} rules\<close>

subsubsection\<open>Invariants\<close>
definition "I_outer s t \<equiv> \<lambda>(i,j,pos).
  (\<forall>ii<i. \<not>sublist_at s t ii) \<and>
  (case pos of None \<Rightarrow> (\<forall>jj<j. t!(i+jj) = s!(jj)) \<and> j < length s
    | Some p \<Rightarrow> p=i \<and> sublist_at s t i)"
text\<open>For the inner loop, we can reuse @{const I_in_na}.\<close>

subsubsection\<open>Algorithm\<close>
text\<open>First, we use the non-evaluable function @{const iblp1} directly:\<close>
definition "kmp s t \<equiv> do {
  ASSERT (s \<noteq> []);
  let i=0;
  let j=0;
  let pos=None;
  (_,_,pos) \<leftarrow> WHILEIT (I_outer s t) (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    ASSERT (i + length s \<le> length t);
    (j,pos) \<leftarrow> WHILEIT (I_in_na s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
      let j=j+1;
      if j=length s then RETURN (j,Some i) else RETURN (j,None)
    }) (j,pos);
    if pos=None then do {
      ASSERT (j < length s);
      let i = i + (j - iblp1 s j + 1);
      let j = max 0 (iblp1 s j - 1); (*max not necessary*)
      RETURN (i,j,None)
    } else RETURN (i,j,Some i)
  }) (i,j,pos);

  RETURN pos
}"

subsubsection\<open>Correctness\<close>
lemma iblp1_j0[simp]: "iblp1 s j = 0 \<longleftrightarrow> j = 0"
  by (cases j) simp_all

lemma j_le_iblp1_le: "j \<le> length s \<Longrightarrow> iblp1 s j \<le> j"
  apply (cases j)
  apply simp_all
  by (metis Suc_leI intrinsic_border_less length_take list.size(3) min.absorb2 nat.simps(3) not_less)

lemma j_le_iblp1_le': "0 < j \<Longrightarrow> j \<le> length s \<Longrightarrow> iblp1 s j - 1 < j"
  by (metis diff_less j_le_iblp1_le le_eq_less_or_eq less_imp_diff_less less_one)

lemma intrinsic_border_less'': "s \<noteq> [] \<Longrightarrow> iblp1 s j - 1 < length s"
  by (cases j) (simp_all add: intrinsic_border_less')

lemma "p576 et seq":
  assumes
    "j \<le> length s" and
    assignments:
    "i' = i + (j + 1 - iblp1 s j)"
    "j' = max 0 (iblp1 s j - 1)"
  shows
    sum_no_decrease: "i' + j' \<ge> i + j" (*Todo: When needed?*) and
    i_increase: "i' > i"
  using assignments by (simp_all add: j_le_iblp1_le[OF assms(1), THEN le_imp_less_Suc])

lemma reuse_matches: 
  assumes j_le: "j \<le> length s"
  and old_matches: "\<forall>jj<j. t ! (i + jj) = s ! jj"
  shows "\<forall>jj<iblp1 s j - 1. t ! (i + (j - iblp1 s j + 1) + jj) = s ! jj"
    (is "\<forall>jj<?j'. t ! (?i' + jj) = s ! jj")
proof (cases "j>0")
  assume "j>0"
  have iblp1_le: "iblp1 s j \<le> j"
    by (simp add: j_le j_le_iblp1_le)
  with old_matches have 1: "\<forall>jj<?j'. t ! (?i' + jj) = s ! (j - iblp1 s j + 1 + jj)"
    by (metis ab_semigroup_add_class.add.commute add.assoc diff_diff_cancel less_diff_conv)
  have [simp]: "length (take j s) = j" "length (intrinsic_border (take j s)) = ?j'"
    by (simp add: j_le) (metis \<open>0 < j\<close> diff_add_inverse2 iblp1.elims nat_neq_iff)
  then have "\<forall>jj<?j'. take j s ! jj = take j s ! (j - (iblp1 s j - 1) + jj)"
    by (metis "needed?" \<open>0 < j\<close> border_positions length_greater_0_conv strict_border_def)
  then have "\<forall>jj<?j'. take j s ! jj = take j s ! (j - iblp1 s j + 1 + jj)"
    by (simp add: iblp1_le)
  then have 2: "\<forall>jj<?j'. s ! (j - iblp1 s j + 1 + jj) = s ! jj"
    using iblp1_le by simp
  from 1 2 show ?thesis by simp
qed simp

theorem shift_safe:
  assumes
    "\<forall>ii<i. \<not>sublist_at s t ii"
    "t!(i+j) \<noteq> s!j" and
    [simp]: "j < length s" and
    matches: "\<forall>jj<j. t!(i+jj) = s!jj"
  defines
    assignment: "i' \<equiv> i + (j - iblp1 s j + 1)"
  shows
    "\<forall>ii<i'. \<not>sublist_at s t ii"
proof (standard, standard)
  fix ii
  assume "ii < i'"
  then consider \<comment>\<open>The position falls into one of three categories:\<close>
    (old) "ii < i" |
    (current) "ii = i" |
    (skipped) "ii > i"
    by linarith
  then show "\<not>sublist_at s t ii"
  proof cases
    case old --\<open>Old position, use invariant.\<close>
    with \<open>\<forall>ii<i. \<not>sublist_at s t ii\<close> show ?thesis by simp
  next
    case current --\<open>The mismatch occurred while testing this alignment.\<close>
    with \<open>t!(i+j) \<noteq> s!j\<close> show ?thesis
      using sublist_all_positions[of s t i] by auto
  next
    case skipped --\<open>The skipped positions.\<close>
    then have "0<j"
      using \<open>ii < i'\<close> assignment by linarith
    then have less_j[simp]: "j + i - ii < j" and le_s: "j + i - ii \<le> length s"
      using \<open>ii < i'\<close> assms(3) skipped by linarith+
    note iblp1_le[simp] = j_le_iblp1_le[OF assms(3)[THEN less_imp_le]]
    have "0 < iblp1 s j"
      using \<open>0 < j\<close> iblp1_j0 neq0_conv by blast
    then have "j + i - ii > iblp1 s j - 1"
      using \<open>ii < i'\<close> assignment iblp1_le by linarith
    then have contradiction_goal: "j + i - ii > length (intrinsic_border (take j s))"
      by (metis (no_types, hide_lams) One_nat_def \<open>0 < j\<close> ab_semigroup_add_class.add.commute add.left_neutral add_Suc diff_Suc_Suc diff_zero gr0_implies_Suc iblp1.simps(2))
    show ?thesis
    proof
      assume "sublist_at s t ii"
      note sublist_all_positions[OF this]
      with le_s have a: "\<forall>jj < j+i-ii. t!(ii+jj) = s!jj"
        by simp
      have ff1: "\<not> ii < i"
        by (metis not_less_iff_gr_or_eq skipped)
      then have "i + (ii - i + jj) = ii + jj" for jj
        by (metis add.assoc add_diff_inverse_nat)
      then have "\<not> jj < j + i - ii \<or> t ! (ii + jj) = s ! (ii - i + jj)" if "ii - i + jj < j" for jj
        using that ff1 by (metis matches)
      then have "\<not> jj < j + i - ii \<or> t ! (ii + jj) = s ! (ii - i + jj)" for jj
        using ff1 by auto
      with matches have "\<forall>jj < j+i-ii. t!(ii+jj) = s!(ii-i+jj)" by metis
      then have "\<forall>jj < j+i-ii. s!jj = s!(ii-i+jj)"
        using a by auto
      then have "\<forall>jj < j+i-ii. (take j s)!jj = (take j s)!(ii-i+jj)"
        using \<open>i<ii\<close> by auto
      with positions_strict_border[of "j+i-ii" "take j s", simplified]
      have "strict_border (take (j+i-ii) s) (take j s)".
      note intrinsic_border_max[OF this]
      also note contradiction_goal
      also have "j+i-ii \<le> length s" by (fact le_s)
      ultimately
      show False by simp
    qed
  qed
qed

lemma kmp_correct: "s \<noteq> []
  \<Longrightarrow> kmp s t \<le> kmp_SPEC s t"
  unfolding kmp_def kmp_SPEC_def I_outer_def I_in_na_def
  apply (refine_vcg
    WHILEIT_rule[where R="measure (\<lambda>(i,_,pos). length t - i + (if pos = None then 1 else 0))"]
    WHILEIT_rule[where R="measure (\<lambda>(j,_::nat option). length s - j)"]
    )
  apply (vc_solve solve: asm_rl)
  subgoal by (metis add_Suc_right all_positions_sublist less_antisym)
  subgoal using less_antisym by blast
  subgoal for i jout j using shift_safe[of i s t j] by fastforce
  subgoal for i jout j using reuse_matches[of j s t i] intrinsic_border_less'' by simp
  subgoal by (auto split: option.splits) (metis sublist_lengths add_less_cancel_right leI le_less_trans)
  done

subsubsection\<open>Storing the @{const iblp1}-values\<close>
text\<open>We refine the algorithm to compute the @{const iblp1}-values only once at the start:\<close>
definition compute_iblp1s_SPEC :: "'a list \<Rightarrow> nat list nres" where
  "compute_iblp1s_SPEC s \<equiv> SPEC (\<lambda>ls. length ls = length s + 1 \<and> (\<forall>j\<le>length s. ls!j = iblp1 s j))"

definition "kmp1 s t \<equiv> do {
  ASSERT (s \<noteq> []);
  let i=0;
  let j=0;
  let pos=None;
  ls \<leftarrow> compute_iblp1s_SPEC (butlast s);(*At the last char, we abort instead.*)
  (_,_,pos) \<leftarrow> WHILEIT (I_outer s t) (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    ASSERT (i + length s \<le> length t);
    (j,pos) \<leftarrow> WHILEIT (I_in_na s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
      let j=j+1;
      if j=length s then RETURN (j,Some i) else RETURN (j,None)
    }) (j,pos);
    if pos=None then do {
      ASSERT (j < length ls);
      let i = i + (j - ls!j + 1);
      let j = max 0 (ls!j - 1); (*max not necessary*)
      RETURN (i,j,None)
    } else RETURN (i,j,Some i)
  }) (i,j,pos);

  RETURN pos
}"

lemma iblp1_butlast[simp]: "j < length s \<Longrightarrow> iblp1 (butlast s) j = iblp1 s j"
  by (cases j) (simp_all add: take_butlast)

lemma kmp1_refine: "kmp1 s t \<le> kmp s t"
  apply (rule refine_IdD)
  unfolding kmp1_def kmp_def
  unfolding Let_def compute_iblp1s_SPEC_def nres_monad_laws
  apply (intro ASSERT_refine_right ASSERT_refine_left)
  apply simp
  apply (rule Refine_Basic.intro_spec_refine)
  apply refine_rcg
  apply refine_dref_type
  apply vc_solve
  done

text\<open>Next, an algorithm that satisfies @{const compute_iblp1s_SPEC}:\<close>
subsection\<open>Computing @{const iblp1}\<close>
subsubsection\<open>Invariants\<close>

definition "I_out_cb s \<equiv> \<lambda>(ls,i,j).
  length s + 1 = length ls \<and>
  (\<forall>jj<j. ls!jj = iblp1 s jj) \<and>
  ls!(j-1) = i \<and>
  0 < j"
definition "I_in_cb s j \<equiv> \<lambda>i.
  if j=1 then i=0 (* first iteration *)
  else
    strict_border (take (i-1) s) (take (j-1) s) \<and>
    iblp1 s j \<le> i + 1"

subsubsection\<open>Algorithm\<close>
definition compute_iblp1s :: "'a list \<Rightarrow> nat list nres" where
  "compute_iblp1s s = do {
  let ls=replicate (length s + 1) 0;(*only the first 0 is needed*)
  let i=0;
  let j=1;
  (ls,_,_) \<leftarrow> WHILEIT (I_out_cb s) (\<lambda>(ls,i,j). j < length ls) (\<lambda>(ls,i,j). do {
    i \<leftarrow> WHILEIT (I_in_cb s j) (\<lambda>i. i>0 \<and> s!(i-1) \<noteq> s!(j-1)) (\<lambda>i. do {
      ASSERT (i-1 < length ls);
      let i=ls!(i-1);
      RETURN i
    }) i;
    let i=i+1;
    ASSERT (j < length ls);
    let ls=ls[j:=i];
    let j=j+1;
    RETURN (ls,i,j)
  }) (ls,i,j);
  
  RETURN ls
}"

subsubsection\<open>Correctness\<close>
lemma take_length_ib[simp]:
  assumes "0 < j" "j \<le> length s"
    shows "take (length (intrinsic_border (take j s))) s = intrinsic_border (take j s)"
proof -
  from assms have "prefix (intrinsic_border (take j s)) (take j s)"
    by (metis "needed?" border_def list.size(3) neq0_conv not_less strict_border_def take_eq_Nil)
  also have "prefix (take j s) s"
    by (simp add: \<open>j \<le> length s\<close> take_is_prefix)
  finally show ?thesis
    by (metis append_eq_conv_conj prefixE)
qed

lemma ib_singleton[simp]: "intrinsic_border [z] = []"
  by (metis intrinsic_border_less length_Cons length_greater_0_conv less_Suc0 list.size(3))

lemma border_butlast: "border xs ys \<Longrightarrow> border (butlast xs) (butlast ys)"
  apply (auto simp: border_def)
   apply (metis butlast_append prefixE prefix_order.eq_refl prefix_prefix prefixeq_butlast)
  apply (metis Sublist.suffix_def append.right_neutral butlast.simps(1) butlast_append)
  done

corollary strict_border_butlast: "xs \<noteq> [] \<Longrightarrow> strict_border xs ys \<Longrightarrow> strict_border (butlast xs) (butlast ys)"
  unfolding strict_border_def by (simp add: border_butlast less_diff_conv)

lemma border_take_lengths: "i \<le> length s \<Longrightarrow> border (take i s) (take j s) \<Longrightarrow> i \<le> j"
  using border_length_le by fastforce

lemma border_step: "border xs ys \<longleftrightarrow> border (xs@[ys!length xs]) (ys@[ys!length xs])"
  apply (auto simp: border_def suffix_def)
  using append_one_prefix prefixE apply fastforce
  using append_prefixD apply blast
  done

corollary strict_border_step: "strict_border xs ys \<longleftrightarrow> strict_border (xs@[ys!length xs]) (ys@[ys!length xs])"
  unfolding strict_border_def using border_step by auto(*or use proof above*)

lemma ib_butlast: "length w \<ge> 2 \<Longrightarrow> length (intrinsic_border w) \<le> length (intrinsic_border (butlast w)) + 1"
proof -
  assume "length w \<ge> 2"
  then have "w \<noteq> []" by auto
  then have "strict_border (intrinsic_border w) w"
    by (fact intrinsic_borderI')
  with \<open>2 \<le> length w\<close> have "strict_border (butlast (intrinsic_border w)) (butlast w)"
    by (metis One_nat_def border_bot.bot.not_eq_extremum butlast.simps(1) len_greater_imp_nonempty length_butlast lessI less_le_trans numerals(2) strict_border_butlast zero_less_diff)
  then have "length (butlast (intrinsic_border w)) \<le> length (intrinsic_border (butlast w))"
    using intrinsic_border_max by blast
  then show ?thesis
    by simp
qed

corollary iblp1_Suc(*rm*): "Suc i \<le> length w \<Longrightarrow> iblp1 w (Suc i) \<le> iblp1 w i + 1"
  apply (cases i)
   apply (simp_all add: take_Suc0)
  by (metis One_nat_def Suc_eq_plus1 Suc_to_right butlast_take diff_is_0_eq ib_butlast length_take min.absorb2 nat.simps(3) not_less_eq_eq numerals(2))

lemma iblp1_step_bound(*rm*):
  assumes "j \<le> length w"
  shows "iblp1 w j \<le> iblp1 w (j-1) + 1"
  using assms[THEN j_le_iblp1_le] iblp1_Suc assms
  by (metis One_nat_def Suc_pred iblp1.elims less_Suc_eq_le zero_less_Suc)

lemma border_take_iblp1: "border (take (iblp1 s i - 1) s ) (take i s)"
  apply (cases i, simp_all)
  by (metis "needed?" border_order.eq_iff border_order.less_imp_le border_positions nat.simps(3) nat_le_linear positions_border take_all take_eq_Nil take_length_ib zero_less_Suc)

corollary iblp1_strict_borderI: "y = iblp1 s (i - 1) \<Longrightarrow> strict_border (take (i - 1) s) (take (j - 1) s) \<Longrightarrow> strict_border (take (y - 1) s) (take (j - 1) s)"
  using border_order.less_le_not_le border_order.order.trans border_take_iblp1 by blast

corollary strict_border_take_iblp1: "0 < i \<Longrightarrow> i \<le> length s \<Longrightarrow> strict_border (take (iblp1 s i - 1) s ) (take i s)"
  by (meson border_order.less_le_not_le border_take_iblp1 border_take_lengths j_le_iblp1_le' leD)

lemma iblp1_max: "j \<le> length s \<Longrightarrow> strict_border b (take j s) \<Longrightarrow> iblp1 s j \<ge> length b + 1"
  by (metis (no_types, lifting) Suc_eq_plus1 Suc_le_eq add_le_cancel_right strict_borderE iblp1.elims intrinsic_border_max length_take min.absorb2)

theorem skipping_ok:
  assumes j_bounds[simp]: "1 < j" "j \<le> length s"
    and mismatch: "s!(i-1) \<noteq> s!(j-1)"
    and greater_checked: "iblp1 s j \<le> i + 1"
    and "strict_border (take (i-1) s) (take (j-1) s)"
  shows "iblp1 s j \<le> iblp1 s (i-1) + 1"
proof (rule ccontr)
  assume "\<not>iblp1 s j \<le> iblp1 s (i-1) + 1"
  then have i_bounds: "0 < i" "i \<le> length s"
    using greater_checked assms(5) take_Nil by fastforce+
  then have i_less_j: "i < j"
    using assms(5) border_length_r_less nz_le_conv_less by auto
  from \<open>\<not>iblp1 s j \<le> iblp1 s (i-1) + 1\<close> greater_checked consider
    (tested) "iblp1 s j = i + 1" --\<open>This contradicts @{thm mismatch}\<close> |
    (skipped) "iblp1 s (i-1) + 1 < iblp1 s j" "iblp1 s j \<le> i"
      --\<open>This contradicts @{thm iblp1_max[of "i-1" s]}\<close>
    by linarith
  then show False
  proof cases
    case tested
    then have "iblp1 s j - 1 = i" by simp
    moreover note border_positions[OF border_take_iblp1[of s j, unfolded this]]
    ultimately have "take j s ! (i-1) = s!(j-1)" using i_bounds i_less_j by simp
    with \<open>i < j\<close> have "s!(i-1) = s!(j-1)"
      by (simp add: less_imp_diff_less)
    with mismatch show False..
  next
    case skipped
    let ?border = "take (i-1) s"
      \<comment>\<open>This border of @{term \<open>take (j-1) s\<close>} could not be extended to a border of @{term \<open>take j s\<close>} due to the mismatch.\<close>
    let ?impossible = "take (iblp1 s j - 2) s"
      \<comment>\<open>A strict border longer than @{term \<open>intrinsic_border ?border\<close>}, a contradiction.\<close>
    have "length (take j s) = j"
      by simp
    have "iblp1 s j - 2 < i - 1"
      using skipped by linarith
    then have less_s: "iblp1 s j - 2 < length s" "i - 1 < length s"
      using \<open>i < j\<close> j_bounds(2) by linarith+
    then have strict: "length ?impossible < length ?border"
      using \<open>iblp1 s j - 2 < i - 1\<close> by auto
    moreover {
      have "prefix ?impossible (take j s)"
        using prefix_length_prefix take_is_prefix
        by (metis (no_types, lifting) \<open>length (take j s) = j\<close> j_bounds(2) diff_le_self j_le_iblp1_le length_take less_s(1) min_simps(2) order_trans)
      moreover have "prefix ?border (take j s)"
        by (metis (no_types, lifting) \<open>length (take j s) = j\<close> diff_le_self i_less_j le_trans length_take less_or_eq_imp_le less_s(2) min_simps(2) prefix_length_prefix take_is_prefix)
      ultimately have "prefix ?impossible ?border"
        using strict less_imp_le_nat prefix_length_prefix by blast
    } moreover {
      have "suffix (take (iblp1 s j - 1) s) (take j s)" using border_take_iblp1
        by (auto simp: border_def)
      note suffix_butlast[OF this]
      then have "suffix ?impossible (take (j-1) s)"
        by (metis One_nat_def j_bounds(2) butlast_take diff_diff_left intrinsic_border_less'' len_greater_imp_nonempty less_or_eq_imp_le less_s(2) one_add_one)
      then have "suffix ?impossible (take (j-1) s)" "suffix ?border (take (j-1) s)"
        using assms(5) by auto
      from suffix_length_suffix[OF this strict[THEN less_imp_le]]
        have "suffix ?impossible ?border".
    }
    ultimately have "strict_border ?impossible ?border"
      unfolding strict_border_def[unfolded border_def] by blast
    note iblp1_max[of "i-1" s, OF _ this]
    then have "length (take (iblp1 s j - 2) s) + 1 \<le> iblp1 s (i-1)"
      using less_imp_le_nat less_s(2) by blast
    then have "iblp1 s j - 1 \<le> iblp1 s (i-1)"
      by (simp add: less_s(1))
    then have "iblp1 s j \<le> iblp1 s (i-1) + 1"
      using le_diff_conv by blast
    with skipped(1) show False
      by linarith
  qed
qed

lemma extend_border:
  assumes "j \<le> length s"
  assumes "s!(i-1) = s!(j-1)"
  assumes "strict_border (take (i-1) s) (take (j-1) s)"
  assumes "iblp1 s j \<le> i + 1"
  shows "iblp1 s j = i + 1"
proof -
  from assms(3) have pos_in_range: "i - 1 < length s " "length (take (i-1) s) = i - 1"
    using border_length_r_less min_less_iff_conj by auto
  with strict_border_step[THEN iffD1, OF assms(3)] have "strict_border (take (i-1) s @ [s!(i-1)]) (take (j-1) s @ [s!(i-1)])"
    by (metis assms(3) border_length_r_less length_take min_less_iff_conj nth_take)
  with pos_in_range have "strict_border (take i s) (take (j-1) s @ [s!(i-1)])"
    by (metis Suc_eq_plus1 Suc_pred add.left_neutral border_bot.bot.not_eq_extremum border_order.less_asym neq0_conv take_0 take_Suc_conv_app_nth)
  then have "strict_border (take i s) (take (j-1) s @ [s!(j-1)])"
    by (simp only: \<open>s!(i-1) = s!(j-1)\<close>)
  then have "strict_border (take i s) (take j s)"
    by (metis One_nat_def Suc_pred assms(1,3) diff_le_self less_le_trans neq0_conv nz_le_conv_less strict_border_imp_nonempty take_Suc_conv_app_nth take_eq_Nil)
  with iblp1_max[OF assms(1) this] have "iblp1 s j \<ge> i + 1"
    using Suc_leI by fastforce
  with \<open>iblp1 s j \<le> i + 1\<close> show ?thesis
    using le_antisym by presburger
qed

lemma computeBorders_correct: "compute_iblp1s s \<le> compute_iblp1s_SPEC s"
  unfolding compute_iblp1s_SPEC_def compute_iblp1s_def I_out_cb_def I_in_cb_def
  apply (simp, refine_vcg
    WHILEIT_rule[where R="measure (\<lambda>(ls,i,j). length s + 1 - j)"]
    WHILEIT_rule[where R="measure id"] \<comment>\<open>@{term \<open>i::nat\<close>} decreases with every iteration.\<close>
    )
                      apply (vc_solve, fold One_nat_def)
  subgoal for b j by (rule strict_border_take_iblp1, auto)
  subgoal by (metis Suc_eq_plus1 iblp1_step_bound less_Suc_eq_le)
  subgoal by fastforce
  subgoal
    by (metis (no_types, lifting) One_nat_def Suc_lessD Suc_pred border_length_r_less iblp1_strict_borderI length_take less_Suc_eq less_Suc_eq_le min.absorb2)
  subgoal for b j i
    by (metis (no_types, lifting) One_nat_def Suc_diff_1 Suc_eq_plus1 Suc_leI border_take_lengths less_Suc_eq_le less_antisym skipping_ok strict_border_def)
  subgoal by (metis Suc_diff_1 border_take_lengths j_le_iblp1_le less_Suc_eq_le strict_border_def)
  subgoal for b j i jj
    by (metis Suc_eq_plus1 Suc_eq_plus1_left add.right_neutral extend_border iblp1_j0 j_le_iblp1_le le_zero_eq less_Suc_eq less_Suc_eq_le nth_list_update_eq nth_list_update_neq)
  subgoal by linarith
  done

subsubsection\<open>Index shift\<close>
text\<open>To avoid inefficiencies, we refine @{const compute_iblp1s} to take @{term s}
instead of @{term \<open>butlast s\<close>} (it still only uses @{term \<open>butlast s\<close>}).\<close>
definition computeBorders2 :: "'a list \<Rightarrow> nat list nres" where
  "computeBorders2 s = do {
  let ls=replicate (length s) 0;
  let i=0;
  let j=1;
  (ls,_,_) \<leftarrow> WHILEIT (I_out_cb (butlast s)) (\<lambda>(b,i,j). j < length b) (\<lambda>(ls,i,j). do {
    ASSERT (j < length ls);
    i \<leftarrow> WHILEIT (I_in_cb (butlast s) j) (\<lambda>i. i>0 \<and> s!(i-1) \<noteq> s!(j-1)) (\<lambda>i. do {
      ASSERT (i-1 < length ls);
      let i=ls!(i-1);
      RETURN i
    }) i;
    let i=i+1;
    ASSERT (j < length ls);
    let ls=ls[j:=i];
    let j=j+1;
    RETURN (ls,i,j)
  }) (ls,i,j);
  
  RETURN ls
}"

lemma computeBorders_inner_bounds: 
  assumes "I_out_cb s (ls,ix,j)"
  assumes "j < length ls"
  assumes "I_in_cb s j i"
  shows "i-1 < length s" "j-1 < length s"
  using assms
    by (auto simp: I_out_cb_def I_in_cb_def split: if_splits)

lemma computeBorders2_ref1: "(s,s') \<in> br butlast (op \<noteq>[]) \<Longrightarrow> computeBorders2 s \<le> \<Down>Id (compute_iblp1s s')"
  unfolding computeBorders2_def compute_iblp1s_def
  apply (refine_rcg)
  apply (refine_dref_type)
  apply (vc_solve simp: in_br_conv)
  subgoal by (metis Suc_pred length_greater_0_conv replicate_Suc)
  subgoal by (metis One_nat_def computeBorders_inner_bounds nth_butlast)
  done

  
corollary computeBorders2_refine'[refine]: 
  assumes "(s,s') \<in> br butlast (op \<noteq>[])"
  shows "computeBorders2 s \<le> \<Down> Id (compute_iblp1s_SPEC s')"
proof -
  note computeBorders2_ref1
  also note computeBorders_correct
  finally show ?thesis using assms by simp
qed
  
subsection\<open>Conflation\<close>
text\<open>We replace @{const compute_iblp1s_SPEC} with @{const compute_iblp1s}\<close>
definition "kmp2 s t \<equiv> do {
  ASSERT (s \<noteq> []);
  let i=0;
  let j=0;
  let pos=None;
  ls \<leftarrow> computeBorders2 s;
  (_,_,pos) \<leftarrow> WHILEIT (I_outer s t) (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    ASSERT (i + length s \<le> length t \<and> pos=None);
    (j,pos) \<leftarrow> WHILEIT (I_in_na s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
      let j=j+1;
      if j=length s then RETURN (j,Some i) else RETURN (j,None)
    }) (j,pos);
    if pos=None then do {
      ASSERT (j < length ls);
      let i = i + (j - ls!j + 1);
      let j = max 0 (ls!j - 1); (*max not necessary*)
      RETURN (i,j,None)
    } else RETURN (i,j,Some i)
  }) (i,j,pos);

  RETURN pos
}"

text\<open>Using @{thm [source] computeBorders2_refine'} (it has attribute @{attribute refine}), the proof is trivial:\<close>
lemma kmp2_refine: "kmp2 s t \<le> kmp1 s t"
  apply (rule refine_IdD)
  unfolding kmp2_def kmp1_def
  apply refine_rcg
  apply refine_dref_type
  apply (vc_solve simp: in_br_conv)
  done

lemma kmp2_correct: "s \<noteq> []
  \<Longrightarrow> kmp2 s t \<le> kmp_SPEC s t"
proof -
  assume "s \<noteq> []"
  have "kmp2 s t \<le> kmp1 s t" by (fact kmp2_refine)
  also have "... \<le> kmp s t" by (fact kmp1_refine)
  also have "... \<le> kmp_SPEC s t" by (fact kmp_correct[OF \<open>s \<noteq> []\<close>])
  finally show ?thesis.
qed

text\<open>For convenience, we also remove the precondition:\<close>
definition "kmp3 s t \<equiv> do {
  if s=[] then RETURN (Some 0) else kmp2 s t
}"

lemma kmp3_correct: "kmp3 s t \<le> kmp_SPEC s t"
  unfolding kmp3_def by (simp add: kmp2_correct) (simp add: kmp_SPEC_def)

section \<open>Refinement to Imperative/HOL\<close>

lemma eq_id_param: "(op =, op =) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp

lemmas in_bounds_aux = computeBorders_inner_bounds[of "butlast s" for s, simplified]

sepref_definition computeBorders2_impl is computeBorders2 :: "(arl_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a array_assn nat_assn"
  unfolding computeBorders2_def
  supply in_bounds_aux[dest]
  supply eq_id_param[where 'a='a, sepref_import_param]
  apply (rewrite array_fold_custom_replicate)
  by sepref
  
  
  
declare computeBorders2_impl.refine[sepref_fr_rules]

sepref_register compute_iblp1s

lemma kmp_inner_in_bound:
  assumes "i + length s \<le> length t"
  assumes "I_in_na s t i (j,None)"
  shows "i + j < length t" "j < length s"
  using assms
  by (auto simp: I_in_na_def)
  
sepref_definition kmp_impl is "uncurry kmp3" :: "(arl_assn id_assn)\<^sup>k *\<^sub>a (arl_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn"
  unfolding kmp3_def kmp2_def
  apply (simp only: max_0L) \<comment>\<open>Avoid the unneeded @{const max}\<close>
  apply (rewrite in "WHILEIT (I_in_na _ _ _) \<hole>" conj_commute)
  apply (rewrite in "WHILEIT (I_in_na _ _ _) \<hole>" short_circuit_conv)
  supply kmp_inner_in_bound[dest]
  supply option.splits[split]
  supply eq_id_param[where 'a='a, sepref_import_param]
  by sepref


export_code kmp_impl in SML_imp module_name KMP

lemma kmp3_correct':
  "(uncurry kmp3, uncurry kmp_SPEC) \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI; clarsimp)
  apply (fact kmp3_correct)
  done

lemmas kmp_impl_correct' = kmp_impl.refine[FCOMP kmp3_correct']

theorem kmp3_impl_correct:
  "< arl_assn id_assn s si * arl_assn id_assn t ti > 
       kmp_impl si ti 
   <\<lambda>r. arl_assn id_assn s si * arl_assn id_assn t ti * \<up>(
      case r of None \<Rightarrow>  \<nexists>i. sublist_at s t i
              | Some i \<Rightarrow> sublist_at s t i \<and> (\<forall>ii<i. \<not> sublist_at s t ii)
    )>\<^sub>t"
  by (sep_auto 
    simp: pure_def kmp_SPEC_def
    split: option.split
    heap:  kmp_impl_correct'[THEN hfrefD, THEN hn_refineD, of "(s,t)" "(si,ti)", simplified])

definition "kmp_string_impl \<equiv> kmp_impl :: (char array \<times> nat) \<Rightarrow> _"

ML_val \<open>
  open File

\<close>

ML_val \<open>
  fun str2arl s = (Array.fromList (String.explode s), @{code nat_of_integer} (String.size s))
  fun kmp s t = map_option (@{code integer_of_nat}) (@{code kmp_string_impl} (str2arl s) (str2arl t) ())

  (*too fast, no warnings*)
  val test1 = let val (s,t) = ("anas","bananas"); val kmp_res1 = timeap_msg "test1_kmp" (kmp s) t; in
  @{assert} (kmp_res1 = kmp_res1(*replace by ... = timeap_msg "test1_nap" (nap s) t*)); kmp_res1 end;
  val test2 = timeap_msg "test2_kmp" (kmp "") "bananas"
  val test3 = timeap_msg "test3_kmp" (kmp "hide_fact") (File.read @{file "~~/src/HOL/Main.thy"})
  (*some(~370) almost(19char)-matches \<longrightarrow> bad for nap*)
  val test4 = timeap_msg "test4_kmp" (kmp
    "\\newcommand{\\isasymproof")
    (File.read @{file "~~/lib/texinputs/isabellesym.sty"})
  (*will it be bad enough for a warning? todo.*)
  (*pattern large \<longrightarrow> bad for kmp*)
  val test5 = timeap_msg "test5_kmp" (kmp
    (File.read @{file "~~/src/Doc/JEdit/document/isabelle-jedit-hdpi.png"}))
    (File.read @{file "~~/src/Doc/JEdit/document/isabelle-jedit-hdpi.png"})
  (*a negative example*)
  val test6 = timeap_msg "test6_kmp" (kmp
    (File.read @{file "~~/src/Doc/JEdit/document/isabelle-jedit-hdpi.png"}))
    "anystring"
  
  (*typical usecase, todo: difference to "hide_fact"-example?*)
  val test7 = let val (s,t) =
    ("basic_entity", File.read @{file "~~/src/Pure/Thy/thy_output.ML"});
  val kmp_res7 = timeap_msg "test7_kmp" (kmp s) t in
  @{assert} (kmp_res7 = kmp_res7); kmp_res7 end
  
  (*todo: example where the alphabet is infinite or where equality takes long*)

\<close>

unused_thms

end
