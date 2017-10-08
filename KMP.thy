
theory KMP
  imports Refine_Imperative_HOL.IICF
    "HOL-Library.Sublist"
    "HOL-Library.Code_Char"
begin

text\<open>Test. @{cite "Refine_Imperative_HOL-AFP"} Working? Test 2 @{cite FPMIS}. Bla @{cite GAD}\<close>

declare len_greater_imp_nonempty[simp del] min_absorb2[simp]
no_notation Ref.update ("_ := _" 62)
lemma nat_min_absorb_Suc[simp]: (*rm?*)
  "a < Suc b \<Longrightarrow> min a b = a"
  "b < Suc a \<Longrightarrow> min a b = b"
  by simp_all

section\<open>Specification\<close>

subsection\<open>Sublist-predicate with a position check\<close>

subsubsection\<open>Definition\<close>

text \<open>One could define\<close>
definition "sublist_at' s t i \<equiv> take (length s) (drop i t) = s"  

text\<open>However, this doesn't handle out-of-bound indexes uniformly:\<close>
value[nbe] "sublist_at' [] [a] 5"
value[nbe] "sublist_at' [a] [a] 5"
value[nbe] "sublist_at' [] [] 5"

text\<open>Instead, we use a recursive definition:\<close>
fun sublist_at :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "sublist_at (s#ss) (t#ts) 0 \<longleftrightarrow> t=s \<and> sublist_at ss ts 0" |
  "sublist_at ss (t#ts) (Suc i) \<longleftrightarrow> sublist_at ss ts i" |
  "sublist_at [] t 0 \<longleftrightarrow> True" |
  "sublist_at _ [] _ \<longleftrightarrow> False"

text\<open>For all relevant cases, both definitions agree:\<close>
lemma "i \<le> length t \<Longrightarrow> sublist_at s t i \<longleftrightarrow> sublist_at' s t i"
  unfolding sublist_at'_def
  by (induction s t i rule: sublist_at.induct) auto

text\<open>However, the new definition has some reasonable properties:\<close>
subsubsection\<open>Properties\<close>
lemma sublist_lengths: "sublist_at s t i \<Longrightarrow> i + length s \<le> length t"
  by (induction s t i rule: sublist_at.induct) auto

lemma Nil_is_sublist: "sublist_at ([] :: 'y list) t i \<longleftrightarrow> i \<le> length t"
  by (induction "[] :: 'y list" t i rule: sublist_at.induct) auto

text\<open>Furthermore, we need:\<close>
lemma sublist_step:
  "\<lbrakk>i + length s < length t; sublist_at s t i; t!(i+length s) = x\<rbrakk> \<Longrightarrow> sublist_at (s@[x]) t i"
  apply (induction s t i rule: sublist_at.induct)
  apply auto
  using sublist_at.elims(3) by fastforce

lemma all_positions_sublist:
"\<lbrakk>i + length s \<le> length t; \<forall>jj<length s. t!(i+jj) = s!jj\<rbrakk> \<Longrightarrow> sublist_at s t i"
proof (induction s rule: rev_induct)
  case Nil
  then show ?case by (simp add: Nil_is_sublist)
next
  case (snoc x xs)
  from \<open>i + length (xs @ [x]) \<le> length t\<close> have "i + length xs \<le> length t" by simp
  moreover have "\<forall>jj<length xs. t ! (i + jj) = xs ! jj"
    by (simp add: nth_append snoc.prems(2))
  ultimately have "sublist_at xs t i"
    using snoc.IH by simp
  then show ?case
    using snoc.prems by (auto intro: sublist_step)
qed

lemma sublist_all_positions: "sublist_at s t i \<Longrightarrow> \<forall>jj<length s. t!(i+jj) = s!jj"
  by (induction s t i rule: sublist_at.induct) (auto simp: nth_Cons')

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

corollary sublist_iff_sublist_at: "Sublist.sublist s t \<longleftrightarrow> (\<exists>i. sublist_at s t i)"
  by (simp add: sublist_at_altdef Sublist.sublist_def)

subsection\<open>Sublist-check algorithms\<close>

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

corollary weak_kmp_SPEC: "kmp_SPEC s t \<le> SPEC (\<lambda>p. p\<noteq>None \<longleftrightarrow> Sublist.sublist s t)"
  by (simp add: kmp_result)

lemmas kmp_SPEC_altdefs =
  kmp_SPEC_def[folded is_arg_min_id]
  kmp_SPEC_def[folded sublist_iff_sublist_at]
  kmp_result

section\<open>Naive algorithm\<close>(*remove section? rename nap \<rightarrow> na / naive_algorithm?*)

text\<open>Since KMP is a direct advancement of the naive "test-all-starting-positions" approach, we provide it here for comparison:\<close>
subsection\<open>Basic form\<close>
definition "I_out_na s t \<equiv> \<lambda>(i,j,found).
  \<not>found \<and> j = 0 \<and> (\<forall>ii<i. \<not>sublist_at s t ii)
  \<or> found \<and> sublist_at s t i"
definition "I_in_na s t i \<equiv> \<lambda>(j,found).
  (\<forall>jj<j. t!(i+jj) = s!(jj)) \<and> (if found then j = length s else j < length s)"

definition "na s t \<equiv> do {
  let i=0;
  let j=0;
  let found=False;
  (_,_,found) \<leftarrow> WHILEIT (I_out_na s t) (\<lambda>(i,j,found). i \<le> length t - length s \<and> \<not>found) (\<lambda>(i,j,found). do {
    (j,found) \<leftarrow> WHILEIT (I_in_na s t i) (\<lambda>(j,found). t!(i+j) = s!j \<and> \<not>found) (\<lambda>(j,found). do {
      let j=j+1;
      if j=length s then RETURN (j,True) else RETURN (j,False)
    }) (j,found);
    if \<not>found then do {
      let i = i + 1;
      let j = 0;
      RETURN (i,j,False)
    } else RETURN (i,j,True)
  }) (i,j,found);

  RETURN found
}"

lemma na_correct: "\<lbrakk>s \<noteq> []; length s \<le> length t\<rbrakk>
  \<Longrightarrow> na s t \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<exists>i. sublist_at s t i))"
  unfolding na_def I_out_na_def I_in_na_def
  apply (refine_vcg 
        WHILEIT_rule[where R="measure (\<lambda>(i,_,found). (length t - i) + (if found then 0 else 1))"]
        WHILEIT_rule[where R="measure (\<lambda>(j,_::bool). length s - j)"]
        ) 
  apply (vc_solve solve: asm_rl)
  subgoal using less_SucE by blast
  subgoal using less_SucE by blast
  subgoal by (metis less_SucE sublist_all_positions)
  subgoal by (simp add: all_positions_sublist)
  subgoal by (meson le_diff_conv2 leI order_trans sublist_lengths)
  done

text\<open>The first precondition cannot be removed without an extra branch: If @{prop \<open>s = []\<close>}, the inner while-condition will access out-of-bound memory. Note however, that @{thm (prem 2) na_correct [no_vars]} is not needed if we use @{type int} or rewrite @{prop \<open>i \<le> length t - length s\<close>} in the first while-condition to @{prop \<open>i + length s \<le> length t\<close>}, which we'll do from now on.\<close>

subsection\<open>A variant returning the position\<close>
definition "I_out_nap s t \<equiv> \<lambda>(i,j,pos).
  (\<forall>ii<i. \<not>sublist_at s t ii) \<and>
  (case pos of None \<Rightarrow> j = 0
    | Some p \<Rightarrow> p=i \<and> sublist_at s t i)"
definition "I_in_nap s t i \<equiv> \<lambda>(j,pos).
  case pos of None \<Rightarrow> j < length s \<and> (\<forall>jj<j. t!(i+jj) = s!(jj))
    | Some p \<Rightarrow> sublist_at s t i"

definition "nap s t \<equiv> do {
  let i=0;
  let j=0;
  let pos=None;
  (_,_,pos) \<leftarrow> WHILEIT (I_out_nap s t) (\<lambda>(i,_,pos). i + length s \<le>length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    (_,pos) \<leftarrow> WHILEIT (I_in_nap s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,_). do {
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

lemma "s \<noteq> []
  \<Longrightarrow> nap s t \<le> kmp_SPEC s t"
  unfolding nap_def kmp_SPEC_def I_out_nap_def I_in_nap_def
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

section\<open>Borders of lists\<close>

definition "border xs ys \<longleftrightarrow> prefix xs ys \<and> suffix xs ys"
definition "strict_border xs ys \<longleftrightarrow> border xs ys \<and> length xs < length ys"
definition "intrinsic_border ls \<equiv> ARG_MAX length b. strict_border b ls"

subsection\<open>Properties\<close>

interpretation border_order: order border strict_border
  by standard (auto simp: border_def suffix_def strict_border_def)
interpretation border_bot: order_bot Nil border strict_border
  by standard (simp add: border_def)

lemma borderE[elim](*rm?*):
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

subsection\<open>Examples\<close>

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

section\<open>Knuth–Morris–Pratt algorithm\<close>

text\<open>"Intrinsic border length plus one" for prefixes\<close>
fun iblp1 :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "iblp1 s 0 = 0" \<comment>\<open>This increments the compare position while @{prop \<open>j=(0::nat)\<close>}\<close> |
  "iblp1 s j = length (intrinsic_border (take j s)) + 1"
  --\<open>Todo: Better name, use @{command definition} and @{const If} instead of fake pattern matching, then prove @{attribute simp} rules\<close>

subsection\<open>Invariants\<close>
definition "I_outer s t \<equiv> \<lambda>(i,j,pos).
  (\<forall>ii<i. \<not>sublist_at s t ii) \<and>
  (case pos of None \<Rightarrow> (\<forall>jj<j. t!(i+jj) = s!(jj)) \<and> j < length s
    | Some p \<Rightarrow> p=i \<and> sublist_at s t i)"
text\<open>For the inner loop, we can reuse @{const I_in_nap}.\<close>

subsection\<open>Algorithm\<close>
text\<open>First, we use the non-evaluable function @{const iblp1} directly:\<close>
definition "kmp s t \<equiv> do {
  ASSERT (s \<noteq> []);
  let i=0;
  let j=0;
  let pos=None;
  (_,_,pos) \<leftarrow> WHILEIT (I_outer s t) (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    ASSERT (i + length s \<le> length t);
    (j,pos) \<leftarrow> WHILEIT (I_in_nap s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
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

lemma shift_safe:
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
  unfolding kmp_def kmp_SPEC_def I_outer_def I_in_nap_def
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

text\<open>We refine the algorithm to compute the @{const iblp1}-values only once at the start:\<close>
definition computeBordersSpec :: "'a list \<Rightarrow> nat list nres" where
  "computeBordersSpec s \<equiv> SPEC (\<lambda>l. length l = length s + 1 \<and> (\<forall>j\<le>length s. l!j = iblp1 s j))"

definition "kmp1 s t \<equiv> do {
  ASSERT (s \<noteq> []);
  let i=0;
  let j=0;
  let pos=None;
  borders \<leftarrow> computeBordersSpec (butlast s);(*At the last char, we abort instead.*)
  (_,_,pos) \<leftarrow> WHILEIT (I_outer s t) (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    ASSERT (i + length s \<le> length t);
    (j,pos) \<leftarrow> WHILEIT (I_in_nap s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
      let j=j+1;
      if j=length s then RETURN (j,Some i) else RETURN (j,None)
    }) (j,pos);
    if pos=None then do {
      ASSERT (j < length borders);
      let i = i + (j - borders!j + 1);
      let j = max 0 (borders!j - 1); (*max not necessary*)
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
  unfolding Let_def computeBordersSpec_def nres_monad_laws
  apply (intro ASSERT_refine_right ASSERT_refine_left)
  apply simp
  apply (rule Refine_Basic.intro_spec_refine)
  apply refine_rcg
  apply refine_dref_type
  apply vc_solve
  done

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

lemma ib1[simp]: "intrinsic_border [z] = []"
  by (metis intrinsic_border_less length_Cons length_ge_1_conv less_Suc0 list.distinct(1) list.size(3))

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

corollary strict_border_step': (*rm*)
  assumes "i \<le> length s"
  shows "strict_border (take i s) (take (j-1) s) \<longleftrightarrow> strict_border (take i s @[s!i]) (take (j-1) s @[s!i])"
proof -
  have "s ! min (length s) i = s ! i"
    by (metis assms min.absorb2)
  moreover
  { assume "min (length s) i < j - 1 \<and> s ! min (length s) i = s ! i"
    then have "take (j - 1) s ! min (length s) i = s ! i"
      by (metis nth_take)
    then have ?thesis
      by (metis (no_types) length_take strict_border_step) }
  ultimately show ?thesis
    by (auto simp: strict_border_def)
qed

lemma intrinsic_border_step: "w \<noteq> [] \<Longrightarrow> intrinsic_border w = r \<Longrightarrow> border (r@[w!length r]) (w@[w!length r])"
  using border_step intrinsic_borderI' strict_border_def by blast

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

thm border_positions
corollary intrinsic_border_positions: "length (intrinsic_border ls) = l
  \<Longrightarrow> \<forall>i<l. ls!i = ls!(length ls - l + i)"
  by (metis add_cancel_left_left border_positions border_step intrinsic_border_step length_0_conv minus_eq)

lemma border_take_iblp1: "border (take (iblp1 s i - 1) s ) (take i s)"
  apply (cases i, simp_all)
  by (metis "needed?" border_order.eq_iff border_order.less_imp_le border_positions nat.simps(3) nat_le_linear positions_border take_all take_eq_Nil take_length_ib zero_less_Suc)

corollary iblp1_strict_borderI: "y = iblp1 s (i - 1) \<Longrightarrow> strict_border (take (i - 1) s) (take (j - 1) s) \<Longrightarrow> strict_border (take (y - 1) s) (take (j - 1) s)"
  using border_order.less_le_not_le border_order.order.trans border_take_iblp1 by blast

corollary strict_border_take_iblp1: "0 < i \<Longrightarrow> i \<le> length s \<Longrightarrow> strict_border (take (iblp1 s i - 1) s ) (take i s)"
  by (meson border_order.less_le_not_le border_take_iblp1 border_take_lengths j_le_iblp1_le' leD)

lemma iblp1_max: "j \<le> length s \<Longrightarrow> strict_border b (take j s) \<Longrightarrow> iblp1 s j \<ge> length b + 1"
  by (metis (no_types, lifting) Suc_eq_plus1 Suc_le_eq add_le_cancel_right strict_borderE iblp1.elims intrinsic_border_max length_take min.absorb2)

text\<open>Next, an algorithm that satisfies @{const computeBordersSpec}:\<close>
subsubsection\<open>Computing @{const iblp1}\<close>

lemma skipping_ok:
  assumes bounds[simp]: "1 < j" "j \<le> length s"
    and mismatch: "s!(x-1) \<noteq> s!(j-1)"
    and greater_checked: "iblp1 s j \<le> x + 1"
    and "strict_border (take (x-1) s) (take (j-1) s)"
  shows "iblp1 s j \<le> iblp1 s (x-1) + 1"
  proof (rule ccontr)
    assume "\<not>iblp1 s j \<le> iblp1 s (x-1) + 1"
    with greater_checked consider
      (tested) "iblp1 s j = x + 1" --\<open>This contradicts @{thm mismatch}\<close> |
      (skipped) "iblp1 s (x-1) + 1 < iblp1 s j" "iblp1 s j \<le> x"
        --\<open>This contradicts @{thm iblp1_max[of "x-1" s]}\<close>
      by linarith
    then show False
    proof cases
      case tested
      then have "x - 1 < length s" "x - 1 < x"
         apply (metis add_diff_cancel_right' bounds(1) bounds(2) intrinsic_border_less'' less_imp_diff_less less_imp_le_nat less_le_trans list.size(3) not_one_le_zero)
        using \<open>\<not> iblp1 s j \<le> iblp1 s (x-1) + 1\<close> greater_checked by linarith
      moreover from tested have "iblp1 s j - 1 = x" by simp
      moreover note border_positions[OF border_take_iblp1[of s j, unfolded this]]
      ultimately have "take j s ! (x-1) = s!(j-1)"
        by simp (metis (no_types, hide_lams) One_nat_def ab_semigroup_add_class.add.commute bounds
            diff_less_mono2 dual_order.strict_trans2 j_le_iblp1_le' leI le_less less_Suc0 minus_eq not_less
            nth_take ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
      with \<open>x - 1 < x\<close> have "s!(x-1) = s!(j-1)"
        by (metis One_nat_def bounds(2) j_le_iblp1_le le_add1 less_le_trans nth_take tested)
      with mismatch show False..
    next
      case skipped
      let ?border = "take (x-1) s"
        \<comment>\<open>This could not be extended to a border of @{term \<open>take j s\<close>} due to the mismatch.\<close>
      let ?impossible = "take (iblp1 s j - 2) s"
        \<comment>\<open>A strict border longer than @{term \<open>intrinsic_border ?border\<close>}, a contradiction.\<close>
      have \<open>x - 1 < j - 1\<close>
        using assms(5) nat_le_linear by fastforce
      have "length (take j s) = j"
        by simp
      have "iblp1 s j - 2 < x - 1"
        using skipped by linarith
      then have less_s: "iblp1 s j - 2 < length s" "x - 1 < length s"
        using \<open>x - 1 < j - 1\<close> bounds(2) by linarith+
      then have strict: "length ?impossible < length ?border"
        using \<open>iblp1 s j - 2 < x - 1\<close> by auto
      moreover {
        have "prefix ?impossible (take j s)"
          using prefix_length_prefix take_is_prefix
          by (metis (no_types, lifting) \<open>length (take j s) = j\<close> bounds(2) diff_le_self j_le_iblp1_le length_take less_s(1) min_simps(2) order_trans)
        moreover have "prefix ?border (take j s)"
          by (metis (no_types, hide_lams) \<open>length (take j s) = j\<close> \<open>x - 1 < j - 1\<close> diff_le_self length_take less_imp_le_nat less_le_trans less_s(2) min_simps(2) prefix_length_prefix take_is_prefix)
        ultimately have "prefix ?impossible ?border"
          using \<open>length ?impossible < length ?border\<close> less_imp_le_nat prefix_length_prefix by blast
      } moreover {
        have "suffix (take (iblp1 s j - 1) s) (take j s)" using border_take_iblp1
          by (auto simp: border_def)
        note suffix_butlast[OF this]
        then have "suffix ?impossible (take (j-1) s)"
          by (metis One_nat_def bounds(2) butlast_take diff_diff_left intrinsic_border_less'' len_greater_imp_nonempty less_or_eq_imp_le less_s(2) one_add_one)
        moreover note \<open>strict_border (take (x-1) s) (take (j-1) s)\<close>
        ultimately have "suffix ?impossible (take (j-1) s)" "suffix ?border (take (j-1) s)"
           apply blast
          using assms(5) by blast
        from suffix_length_suffix[OF this strict[THEN less_imp_le]]
          have "suffix ?impossible ?border".
      }
      ultimately have "strict_border ?impossible ?border"
        unfolding strict_border_def[unfolded border_def] by blast
      note iblp1_max[of "x-1" s, OF _ this]
      then have "length (take (iblp1 s j - 2) s) + 1 \<le> iblp1 s (x-1)"
        using less_imp_le_nat less_s(2) by blast
      then have "iblp1 s j - 1 \<le> iblp1 s (x-1)"
        by (simp add: less_s(1))
      then have "iblp1 s j \<le> iblp1 s (x-1) + 1"
        using le_diff_conv by blast
      with skipped(1) show False
        by linarith
    qed
  qed

lemma extend_border:
  assumes "j \<le> length s"
  assumes "s!(x-1) = s!(j-1)"
  assumes "strict_border (take (x-1) s) (take (j-1) s)"
  assumes "iblp1 s j \<le> x + 1"
  shows "iblp1 s j = x + 1"
proof -
  have i'_lower: "x - 1 < length s "
    using assms(3) border_length_r_less min_less_iff_conj by auto
  from  assms(3) have "border (take (x-1) s @ [s!(x-1)]) (take (j-1) s @ [s!(x-1)])"
    by (metis border_order.less_imp_le i'_lower less_imp_le_nat strict_border_step')
  then have "border (take x s) (take (j-1) s @ [s!(x-1)])"
    by (metis Suc_diff_Suc Suc_eq_plus1 add.left_neutral border_bot.bot.extremum diff_zero i'_lower length_greater_0_conv length_take min_less_iff_conj take_Suc_conv_app_nth)
  with \<open>s!(x-1) = s!(j-1)\<close> have "border (take x s) (take (j-1) s @ [s!(j-1)])" by auto
  then have "border (take x s) (take j s)"
    by (metis One_nat_def Suc_pred assms(1) assms(3) border_length_r_less diff_le_self length_take less_le_trans min_less_iff_conj nz_le_conv_less take_Suc_conv_app_nth zero_less_diff)
  moreover have "length (take x s) < length (take j s)
    "apply (cases "x=0")
    using assms(3) le_numeral_extra(1) apply auto[1]
    using assms(1) assms(3) butlast_take gr_zeroI apply auto
    done
  ultimately have ib_candidate: "strict_border (take x s) (take j s)"
    unfolding strict_border_def by auto
  then have "iblp1 s j \<ge> x + 1" using iblp1_max[OF _ ib_candidate]
    using Suc_leI assms(1) by fastforce
  with \<open>iblp1 s j \<le> x + 1\<close> show ?thesis
    using le_antisym by presburger
qed

definition "I_out_cb s \<equiv> \<lambda>(b,i,j).
  length s + 1 = length b \<and>
  (\<forall>jj<j. b!jj = iblp1 s jj) \<and>
  b!(j-1) = i \<and>
  0 < j"
definition "I_in_cb s j \<equiv> \<lambda>i.
  if j=1 then i=0 (* first iteration *)
  else
    strict_border (take (i-1) s) (take (j-1) s) \<and>
    iblp1 s j \<le> i + 1"

definition computeBorders :: "'a list \<Rightarrow> nat list nres" where
  "computeBorders s = do {
  let b=replicate (length s + 1) 0;(*only the first 0 is needed*)
  let i=0;
  let j=1;
  (b,_,_) \<leftarrow> WHILEIT (I_out_cb s) (\<lambda>(b,i,j). j < length b) (\<lambda>(b,i,j). do {
    i \<leftarrow> WHILEIT (I_in_cb s j) (\<lambda>i. i>0 \<and> s!(i-1) \<noteq> s!(j-1)) (\<lambda>i. do {
      ASSERT (i-1 < length b);
      let i=b!(i-1);
      RETURN i
    }) i;
    let i=i+1;
    ASSERT (j < length b);
    let b=b[j:=i];
    let j=j+1;
    RETURN (b,i,j)
  }) (b,i,j);
  
  RETURN b
}"

lemma computeBorders_correct: "computeBorders s \<le> computeBordersSpec s"
  unfolding computeBordersSpec_def computeBorders_def I_out_cb_def I_in_cb_def
  apply (simp, refine_vcg
    WHILEIT_rule[where R="measure (\<lambda>(b,i,j). length s + 1 - j)"]
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

text\<open>To avoid inefficiencies, we refine @{const computeBorders} to take @{term s}
instead of @{term \<open>butlast s\<close>} (it still only uses @{term \<open>butlast s\<close>}).\<close>
definition computeBorders2 :: "'a list \<Rightarrow> nat list nres" where
  "computeBorders2 s = do {
  let b=replicate (length s) 0;
  let i=0;
  let j=1;
  (b,_,_) \<leftarrow> WHILEIT (I_out_cb (butlast s)) (\<lambda>(b,i,j). j < length b) (\<lambda>(b,i,j). do {
    ASSERT (j < length b);
    i \<leftarrow> WHILEIT (I_in_cb (butlast s) j) (\<lambda>i. i>0 \<and> s!(i-1) \<noteq> s!(j-1)) (\<lambda>i. do {
      ASSERT (i-1 < length b);
      let i=b!(i-1);
      RETURN i
    }) i;
    let i=i+1;
    ASSERT (j < length b);
    let b=b[j:=i];
    let j=j+1;
    RETURN (b,i,j)
  }) (b,i,j);
  
  RETURN b
}"

lemma computeBorders_inner_bounds: 
  assumes "I_out_cb s (b,ix,j)"
  assumes "j < length b"
  assumes "I_in_cb s j i"
  shows "i-1 < length s" "j-1 < length s"
  using assms
    by (auto simp: I_out_cb_def I_in_cb_def split: if_splits)

lemma computeBorders2_ref1: "(s,s') \<in> br butlast (op \<noteq>[]) \<Longrightarrow> computeBorders2 s \<le> \<Down>Id (computeBorders s')"
  unfolding computeBorders2_def computeBorders_def
  apply (refine_rcg)
  apply (refine_dref_type)
  apply (vc_solve simp: in_br_conv)
  subgoal by (metis Suc_pred length_greater_0_conv replicate_Suc)
  subgoal by (metis One_nat_def computeBorders_inner_bounds nth_butlast)
  done

  
corollary computeBorders2_refine'[refine]: 
  assumes "(s,s') \<in> br butlast (op \<noteq>[])"
  shows "computeBorders2 s \<le> \<Down> Id (computeBordersSpec s')"
proof -
  note computeBorders2_ref1
  also note computeBorders_correct
  finally show ?thesis using assms by simp
qed
  
subsection\<open>Final refinement\<close>
text\<open>We replace @{const computeBordersSpec} with @{const computeBorders}\<close>
definition "kmp2 s t \<equiv> do {
  ASSERT (s \<noteq> []);
  let i=0;
  let j=0;
  let pos=None;
  borders \<leftarrow> computeBorders2 s;
  (_,_,pos) \<leftarrow> WHILEIT (I_outer s t) (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    ASSERT (i + length s \<le> length t \<and> pos=None);
    (j,pos) \<leftarrow> WHILEIT (I_in_nap s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
      let j=j+1;
      if j=length s then RETURN (j,Some i) else RETURN (j,None)
    }) (j,pos);
    if pos=None then do {
      ASSERT (j < length borders);
      let i = i + (j - borders!j + 1);
      let j = max 0 (borders!j - 1); (*max not necessary*)
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

definition "kmp3 s t \<equiv> do {
  if s=[] then RETURN (Some 0) else kmp2 s t
}"

lemma kmp3_correct: "kmp3 s t \<le> kmp_SPEC s t"
  unfolding kmp3_def by (simp add: kmp2_correct) (simp add: kmp_SPEC_def)

(*Todo: Algorithm for the set of all positions. Then: No break-flag needed, and no case distinction in the specification.*)
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

sepref_register computeBorders

lemma kmp_inner_in_bound:
  assumes "i + length s \<le> length t"
  assumes "I_in_nap s t i (j,None)"
  shows "i + j < length t" "j < length s"
  using assms
  by (auto simp: I_in_nap_def)
  
sepref_definition kmp_impl is "uncurry kmp3" :: "(arl_assn id_assn)\<^sup>k *\<^sub>a (arl_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn"
  unfolding kmp3_def kmp2_def
  apply (simp only: max_0L) \<comment>\<open>Avoid the unneeded @{const max}\<close>
  apply (rewrite in "WHILEIT (I_in_nap _ _ _) \<hole>" conj_commute)
  apply (rewrite in "WHILEIT (I_in_nap _ _ _) \<hole>" short_circuit_conv)
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
