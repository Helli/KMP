theory KMP
  imports "$AFP/Refine_Imperative_HOL/IICF/IICF"
    "~~/src/HOL/Library/Sublist"
begin

section\<open>Addition to @{theory "Sublist"}?\<close>
  lemma strict_suffix_altdef: "strict_suffix xs ys \<longleftrightarrow> suffix xs ys \<and> xs \<noteq> ys"
    using strict_suffix_def strict_suffix_imp_suffix suffixE by fastforce

section\<open>Additions to @{theory "IICF_List"} and @{theory "IICF_Array"}\<close>
  sepref_decl_op list_upt: upt :: "nat_rel \<rightarrow> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_rel".
  
  definition array_upt :: "nat \<Rightarrow> nat \<Rightarrow> nat array Heap" where
    "array_upt m n = Array.make (n-m) (\<lambda>i. i + m)"
  
  lemma map_plus_upt: "map (\<lambda>i. i + a) [0..<b - a] = [a..<b]"
    by (induction b) (auto simp: map_add_upt)
  
  lemma array_upt_hnr_aux: "(uncurry array_upt, uncurry (RETURN oo op_list_upt)) \<in> nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a is_array"
    by sepref_to_hoare (sep_auto simp: array_upt_def array_assn_def is_array_def map_plus_upt)
  
  lemma fold_array_assn_alt: "hr_comp is_array (\<langle>R\<rangle>list_rel) = array_assn (pure R)"
    unfolding array_assn_def by auto
  
  context
    notes [fcomp_norm_unfold] = fold_array_assn_alt
  begin
    sepref_decl_impl (no_register) array_upt: array_upt_hnr_aux.
  end
  
  definition [simp]: "op_array_upt \<equiv> op_list_upt"
  sepref_register op_array_upt
  lemma array_fold_custom_upt:
    "upt = op_array_upt"
    "op_list_upt = op_array_upt"
    "mop_list_upt = RETURN oo op_array_upt"
    by (auto simp: op_array_upt_def intro!: ext)
  lemmas array_upt_custom_hnr[sepref_fr_rules] = array_upt_hnr[unfolded array_fold_custom_upt]
  
  text\<open>Is this generalisation of @{thm nth_drop} useful?\<close>
  lemma nth_drop'[simp]: "n \<le> length xs \<Longrightarrow> drop n xs ! i = xs ! (n + i)"
  apply (induct n arbitrary: xs, auto)
   apply (case_tac xs, auto)
  done
    (*by (metis append_take_drop_id length_take min.absorb2 nth_append_length_plus)*)
  thm nth_drop[of _ i] add_leD1[of _ i, THEN nth_drop'[of _ _ i]]

section\<open>Isabelle2017\<close>

  text\<open>From theory @{theory Lattices_Big}:\<close>
  definition is_arg_min :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
    "is_arg_min f P x = (P x \<and> \<not>(\<exists>y. P y \<and> f y < f x))"
    \<comment>\<open>abbreviation if @{term \<open>f = id\<close>}?\<close>
  text\<open>Is this useful?\<close>
  lemma "\<exists>x. P x \<Longrightarrow> is_arg_min id P (Min {x. P x})"
    oops

section\<open>Definition "substring"\<close>
  definition "is_substring_at' s t i \<equiv> take (length s) (drop i t) = s"  
  
  text\<open>Problem:\<close>
  value "is_substring_at' [] [a] 5"
  value "is_substring_at' [a] [a] 5"
  value "is_substring_at' [] [] 3"
  text\<open>Not very intuitive...\<close>
  
  text\<open>For the moment, we use this instead:\<close>
  fun is_substring_at :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
    t1: "is_substring_at (s#ss) (t#ts) 0 \<longleftrightarrow> t=s \<and> is_substring_at ss ts 0" |
    t2: "is_substring_at ss (t#ts) (Suc i) \<longleftrightarrow> is_substring_at ss ts i" |
    "is_substring_at [] t 0 \<longleftrightarrow> True" |
    "is_substring_at _ [] _ \<longleftrightarrow> False"

  lemmas [code del] = t1 t2
    
  lemma [code]: "is_substring_at ss (t#ts) i \<longleftrightarrow> (if i=0 \<and> ss\<noteq>[] then t=hd ss \<and> is_substring_at (tl ss) ts 0 else is_substring_at ss ts (i-1))"  
    by (cases ss; cases i; auto)
  
  text\<open>For all relevant cases, both definitions agree:\<close>
  lemma "i \<le> length t \<Longrightarrow> is_substring_at s t i \<longleftrightarrow> is_substring_at' s t i"
    unfolding is_substring_at'_def
    by (induction s t i rule: is_substring_at.induct) auto
  
  text\<open>However, the new definition has some reasonable properties:\<close>
  lemma substring_lengths: "is_substring_at s t i \<Longrightarrow> i + length s \<le> length t"
    apply (induction s t i rule: is_substring_at.induct)
    apply simp_all
    done
  
  lemma Nil_is_substring: "i \<le> length t \<longleftrightarrow> is_substring_at ([] :: 'y list) t i"
    by (induction "[] :: 'y list" t i rule: is_substring_at.induct) auto
  
  text\<open>Furthermore, we need:\<close>
  lemma substring_step:
    "\<lbrakk>i + length s < length t; is_substring_at s t i; t!(i+length s) = x\<rbrakk> \<Longrightarrow> is_substring_at (s@[x]) t i"
    apply (induction s t i rule: is_substring_at.induct)
    apply auto
    using is_substring_at.elims(3) by fastforce
  
  lemma all_positions_substring:
  "\<lbrakk>i + length s \<le> length t; \<forall>j'<length s. t!(i+j') = s!j'\<rbrakk> \<Longrightarrow> is_substring_at s t i"
  proof (induction s rule: rev_induct)
    case Nil
    then show ?case by (simp add: Nil_is_substring)
  next
    case (snoc x xs)
    from \<open>i + length (xs @ [x]) \<le> length t\<close> have "i + length xs \<le> length t" by simp
    moreover have "\<forall>j'<length xs. t ! (i + j') = xs ! j'"
      by (simp add: nth_append snoc.prems(2))
    ultimately have f: "is_substring_at xs t i"
      using snoc.IH by simp
    show ?case
      apply (rule substring_step)
      using snoc.prems(1) snoc.prems(2) apply auto[]
      apply (fact f)
      by (simp add: snoc.prems(2))
  qed
  
  lemma substring_all_positions:
    "is_substring_at s t i \<Longrightarrow> \<forall>j'<length s. t!(i+j') = s!j'"
    by (induction s t i rule: is_substring_at.induct)
      (auto simp: nth_Cons')
  
  text\<open>Other characterisations:\<close>
  fun slice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" 
    where
    "slice (x#xs) (Suc n) l = slice xs n l"
  | "slice (x#xs) 0 (Suc l) = x # slice xs 0 l"  
  | "slice _ _ _ = []"  
  
  lemma slice_char_aux: "is_substring_at s t 0 \<longleftrightarrow> s = slice t 0 (length s)"
    apply (induction t arbitrary: s)
    subgoal for s by (cases s) auto  
    subgoal for _ _ s by (cases s) auto  
    done    
  
  lemma slice_char: "i\<le>length t \<Longrightarrow> is_substring_at s t i \<longleftrightarrow> s = slice t i (length s)"
    apply (induction s t i rule: is_substring_at.induct) 
    apply (auto simp: slice_char_aux)
    done
  
  text\<open>In the style of @{theory Sublist} (compare @{const prefix}, @{const suffix} etc.):\<close>
  lemma substring_altdef: "is_substring_at s t i \<longleftrightarrow> (\<exists>xs ys. xs@s@ys = t \<and> length xs = i)"
  proof (induction s t i rule: is_substring_at.induct)
    case (2 ss t ts i)
    show "is_substring_at ss (t#ts) (Suc i) \<longleftrightarrow> (\<exists>xs ys. xs@ss@ys = t#ts \<and> length xs = Suc i)"
      (is "?lhs \<longleftrightarrow> ?rhs")
    proof
      assume ?lhs
      then have "is_substring_at ss ts i" by simp
      with "2.IH" obtain xs where "\<exists>ys. ts = xs@ss@ys \<and> i = length xs" by auto
      then have "\<exists>ys. (t#xs)@ss@ys = t#ts \<and> length (t#xs) = Suc i" by auto
      then show ?rhs by blast
    next
      assume ?rhs
      then obtain xs where "\<exists>ys. xs@ss@ys = t#ts \<and> length xs = Suc i" by blast
      then have "\<exists>ys. (tl xs)@ss@ys = ts \<and> length (tl xs) = i"
        by (metis Suc_length_conv len_greater_imp_nonempty list.sel(3) tl_append2 zero_less_Suc)
      then have "\<exists>xs ys. xs@ss@ys = ts \<and> length xs = i" by blast
      with "2.IH" show ?lhs by simp
    qed
  qed auto
  (*Todo: fifth alternative: inductive is_substring_at*)

section\<open>Naive algorithm\<close>
  
  text\<open>Since KMP is a direct advancement of the naive "test-all-starting-positions" approach, we provide it here for comparison:\<close>
subsection\<open>Basic form\<close>
  definition "I_out_na t s \<equiv> \<lambda>(i,j,found).
    \<not>found \<and> j = 0 \<and> (\<forall>i'<i. \<not>is_substring_at s t i')
    \<or> found \<and> is_substring_at s t i"
  definition "I_in_na t s iout \<equiv> \<lambda>(j,found).
    \<not>found \<and> j < length s \<and> (\<forall>j'<j. t!(iout+j') = s!(j'))
    \<or> found \<and> j = length s \<and> is_substring_at s t iout"
  
  definition "na t s \<equiv> do {
    let i=0;
    let j=0;
    let found=False;
    (_,_,found) \<leftarrow> WHILEIT (I_out_na t s) (\<lambda>(i,j,found). i \<le> length t - length s \<and> \<not>found) (\<lambda>(i,j,found). do {
      (j,found) \<leftarrow> WHILEIT (I_in_na t s i) (\<lambda>(j,found). t!(i+j) = s!j \<and> \<not>found) (\<lambda>(j,found). do {
        (*ToDo: maybe instead of \<not>found directly query j<length s ?*)
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
  
  lemma "\<lbrakk>s \<noteq> []; length s \<le> length t\<rbrakk>
    \<Longrightarrow> na t s \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<exists>i. is_substring_at s t i))"
    unfolding na_def I_out_na_def I_in_na_def
    apply (refine_vcg 
          WHILEIT_rule[where R="measure (\<lambda>(i,_,found). (length t - i) + (if found then 0 else 1))"]
          WHILEIT_rule[where R="measure (\<lambda>(j,_::bool). length s - j)"]
          ) 
    apply (vc_solve solve: asm_rl)
    subgoal by (metis Nat.le_diff_conv2 all_positions_substring less_SucE)
    subgoal using less_Suc_eq apply blast done
    subgoal by (metis less_SucE substring_all_positions)
    subgoal by (meson le_diff_conv2 leI order_trans substring_lengths)
    done
  
  text\<open>The first precondition cannot be removed without an extra branch: If @{term \<open>s = []\<close>}, the inner while-condition will access out-of-bound memory. Note however, that @{term \<open>length s \<le> length t\<close>} is not needed if we use @{type int} or rewrite @{term \<open>i \<le> length t - length s\<close>} in the first while-condition to @{term \<open>i + length s \<le> length t\<close>}, which we'll do from now on.\<close>
  
subsection\<open>A variant returning the position\<close>
  definition "I_out_nap t s \<equiv> \<lambda>(i,j,pos).
    (\<forall>i'<i. \<not>is_substring_at s t i') \<and>
    (case pos of None \<Rightarrow> j = 0
      | Some p \<Rightarrow> p=i \<and> is_substring_at s t i)"
  definition "I_in_nap t s iout \<equiv> \<lambda>(j,pos).
    case pos of None \<Rightarrow> j < length s \<and> (\<forall>j'<j. t!(iout+j') = s!(j'))
      | Some p \<Rightarrow> is_substring_at s t iout"

  definition "nap t s \<equiv> do {
    let i=0;
    let j=0;
    let pos=None;
    (_,_,pos) \<leftarrow> WHILEIT (I_out_nap t s) (\<lambda>(i,_,pos). i + length s \<le>length t \<and> pos=None) (\<lambda>(i,j,pos). do {
      (_,pos) \<leftarrow> WHILEIT (I_in_nap t s i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,_). do {
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
    \<Longrightarrow> nap t s \<le> SPEC (\<lambda>None \<Rightarrow> \<nexists>i. is_substring_at s t i | Some i \<Rightarrow> is_substring_at s t i \<and> (\<forall>i'<i. \<not>is_substring_at s t i'))"
    unfolding nap_def I_out_nap_def I_in_nap_def
    apply (refine_vcg
      WHILEIT_rule[where R="measure (\<lambda>(i,_,pos). length t - i + (if pos = None then 1 else 0))"]
      WHILEIT_rule[where R="measure (\<lambda>(j,_::nat option). length s - j)"]
      )
    apply (vc_solve solve: asm_rl)
    subgoal by (metis add_Suc_right all_positions_substring less_antisym)
    subgoal using less_Suc_eq by blast
    subgoal by (metis less_SucE substring_all_positions)
    subgoal by (auto split: option.splits) (metis substring_lengths add_less_cancel_right leI le_less_trans)
    done

section\<open>Knuth–Morris–Pratt algorithm\<close>
subsection\<open>Auxiliary definitions\<close>
  text\<open>Borders of words\<close>
  definition "border r w \<longleftrightarrow> prefix r w \<and> suffix r w"
  definition "strict_border xs ys \<longleftrightarrow> border xs ys \<and> xs \<noteq> ys"(*Try altdef here?*)
  
  interpretation border_order: order border strict_border
    by (standard, auto simp: border_def suffix_def strict_border_def)
  interpretation border_bot: order_bot Nil border strict_border
    by standard (simp add: border_def)
  (*Above interpretations useful? Or provide @{prop "border [] w"} {prop "border w w"} directly?*)
  
  lemma substring_unique: "\<lbrakk>is_substring_at s t i; is_substring_at s' t i; length s = length s'\<rbrakk> \<Longrightarrow> s = s'"
    by (metis nth_equalityI substring_all_positions)
  
  lemma strict_border_prefix: "strict_border r w \<Longrightarrow> strict_prefix r w"
    by (auto simp: strict_border_def border_def)
  lemma strict_border_suffix: "strict_border r w \<Longrightarrow> strict_suffix r w"
    by (auto simp: strict_border_def border_def strict_suffix_altdef)
  
  lemma border_length_le: "border r w \<Longrightarrow> length r \<le> length w"
    unfolding border_def by (simp add: prefix_length_le)
  lemma border_length_less: "strict_border r w \<Longrightarrow> length r < length w"
    by (auto simp: strict_border_def border_def prefix_def)
  
  lemma border_unique: "\<lbrakk>border r w; border r' w; length r = length r'\<rbrakk> \<Longrightarrow> r = r'"
    unfolding border_def by (metis order_mono_setup.refl prefix_length_prefix prefix_order.eq_iff)
  
  lemma border_lengths_differ: "\<lbrakk>border r w; border r' w; r\<noteq>r'\<rbrakk> \<Longrightarrow> length r \<noteq> length r'"
    using border_unique by auto
  
  lemma border_length_r_less: "\<forall>r. strict_border r w \<longrightarrow> length r < length w"
    using border_length_less by auto
  
  lemma strict_border_altdef: "strict_border r w \<longleftrightarrow> border r w \<and> length r < length w"
    using border_length_r_less border_order.le_less by blast
  
  lemma border_positions: "border r w \<Longrightarrow> \<forall>j<length r. w!j = w!(length w - length r + j)" unfolding border_def
    by (metis diff_add_inverse diff_add_inverse2 length_append not_add_less1 nth_append prefixE suffixE)
  
  lemmas nth_stuff = nth_take nth_take_lemma nth_equalityI
  
  (*Todo: swap names, add i+\<dots>, decide whether w instead of x and w is enough*)
  lemma all_positions_drop_length_take: "\<lbrakk>i \<le> length w; i \<le> length x;
    \<forall>j<i. x ! j = w ! (length w + j - i)\<rbrakk>
      \<Longrightarrow> drop (length w - i) w = take i x"
    by (cases "i = length x") (simp_all add: nth_equalityI)
  
  lemma all_positions_suffix_take: "\<lbrakk>i \<le> length w; i \<le> length x;
    \<forall>j<i. x ! j = w ! (length w + j - i)\<rbrakk>
      \<Longrightarrow> suffix (take i x) w"
    by (metis all_positions_drop_length_take suffix_drop)
  
  thm suffix_drop take_is_prefix (* That naming -.- *)
  
  lemma positions_border: "\<forall>j<i. w!j = w!(length w - i + j) \<Longrightarrow> border (take i w) w"
    by (cases "i < length w") (simp_all add: border_def all_positions_suffix_take take_is_prefix)
  
  corollary positions_strict_border: "i < length w \<Longrightarrow> \<forall>j<i. w!j = w!(length w - i + j) \<Longrightarrow> strict_border (take i w) w"
    by (metis length_take min_simps(2) nat_neq_iff positions_border strict_border_def)

subsection\<open>Greatest and Least\<close>
  lemma GreatestM_natI2:
    fixes m::"_\<Rightarrow>nat"
    assumes "P x"
      and "\<forall>y. P y \<longrightarrow> m y < b"
      and "\<And>x. P x \<Longrightarrow> Q x"
    shows "Q (GreatestM m P)"
  by (fact GreatestM_natI[OF assms(1,2), THEN assms(3)])
  
  lemma Greatest_nat_Least:
    fixes m::"_\<Rightarrow>nat"
    assumes "\<forall>y. P y \<longrightarrow> m y \<le> b"
    shows "GreatestM m P = LeastM (\<lambda>a. b - m a) P"
    proof -
    have a: "(\<forall>y. P y \<longrightarrow> b - m x \<le> b - m y) \<longleftrightarrow> (\<forall>y. P y \<longrightarrow> m y \<le> m x)" for x
      using assms diff_le_mono2 by fastforce
    show ?thesis unfolding LeastM_def GreatestM_def a..
  qed
  
  lemma Least_nat_Greatest:
    fixes m::"_\<Rightarrow>nat"
    assumes "\<forall>y. P y \<longrightarrow> m y < b"
    shows "LeastM m P = GreatestM (\<lambda>a. b - m a) P"
  proof -
    have a: "(\<forall>y. P y \<longrightarrow> b - m y \<le> b - m x) \<longleftrightarrow> (\<forall>y. P y \<longrightarrow> m x \<le> m y)" for x
      using assms diff_le_mono2 by force
    show ?thesis unfolding LeastM_def GreatestM_def a..
  qed
  
  lemmas least_equality = some_equality[of "\<lambda>x. P x \<and> (\<forall>y. P y \<longrightarrow> m x \<le> m y)" for P m, folded LeastM_def, simplified]
  lemmas greatest_equality = some_equality[of "\<lambda>x. P x \<and> (\<forall>y. P y \<longrightarrow> m y \<le> m x)" for P m, folded GreatestM_def, no_vars]
  
  definition "intrinsic_border w \<equiv> GREATEST r WRT length . strict_border r w"
  
  definition "intrinsic_border' r w \<longleftrightarrow> border r w \<and> r\<noteq>w \<and>
    (\<nexists>r'. border r' w \<and> r'\<noteq>w \<and> length r < length r')"
  
  lemma ib'_ib: "w \<noteq> [] \<Longrightarrow> intrinsic_border' (intrinsic_border w) w"
  unfolding intrinsic_border_def strict_border_def intrinsic_border'_def
  apply (rule conjI)
    apply (rule GreatestM_natI2[of "\<lambda>r. border r w \<and> r\<noteq>w" "[]" length "length w"])
     apply (simp_all add: border_length_r_less[unfolded strict_border_def])[3]
    apply (rule conjI)
    apply (rule GreatestM_natI2[of "\<lambda>r. border r w \<and> r\<noteq>w" "[]" length "length w"])
     apply (simp_all add: border_length_r_less[unfolded strict_border_def])[3]
    apply auto
  using GreatestM_nat_le[OF _ border_length_r_less[unfolded strict_border_def], of _ w]
    by (simp add: leD)
  
  lemma ib'_unique: "\<lbrakk>intrinsic_border' r w; intrinsic_border' r' w\<rbrakk> \<Longrightarrow> r = r'"
    by (metis border_unique intrinsic_border'_def nat_neq_iff)
  
  lemma ib'_length_r: "intrinsic_border' r w \<Longrightarrow> length r < length w"
    by (simp add: border_length_r_less intrinsic_border'_def strict_border_def)
  
  lemma "needed?": "w \<noteq> [] \<Longrightarrow> strict_border (intrinsic_border w) w"
    (*equivalent to intrinsic_borderI'*)
    unfolding intrinsic_border_def
    thm GreatestM_natI[of _ "[]"]
    apply (rule GreatestM_natI[of _ "[]"])
     apply (simp add: border_bot.bot.not_eq_extremum)
    using border_length_less apply auto
      done
  
  lemmas intrinsic_borderI = GreatestM_natI[of "\<lambda>r. strict_border r w" "[]" length "length w", OF _ border_length_r_less, folded intrinsic_border_def] for w
  
  lemmas sigh = border_bot.bot.not_eq_extremum[THEN iffD1]
  lemmas intrinsic_borderI' = sigh[THEN intrinsic_borderI]
  
  lemmas intrinsic_border_greatest = GreatestM_nat_le[of "\<lambda>r. strict_border r w" _ length "length w", OF _ border_length_r_less, folded intrinsic_border_def] for w
  
  lemma intrinsic_border_less: "w \<noteq> [] \<Longrightarrow> length (intrinsic_border w) < length w"
    using intrinsic_borderI[of w] border_length_r_less "needed?" by blast
  
  lemma intrinsic_border_less': "j > 0 \<Longrightarrow> w \<noteq> [] \<Longrightarrow> length (intrinsic_border (take j w)) < length w"
    by (metis intrinsic_border_less length_take less_not_refl2 min_less_iff_conj take_eq_Nil)
  
  text\<open>"Intrinsic border length plus one" for prefixes\<close>
  fun iblp1 :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
    "iblp1 s 0 = 0"\<comment>\<open>This increments the compare position while \<^term>\<open>j=0\<close>\<close> |
    "iblp1 s j = length (intrinsic_border (take j s)) + 1"
    --\<open>Todo: Better name, replace +1 with Suc\<close>
  
  lemma iblp1_j0: "iblp1 s j = 0 \<longleftrightarrow> j = 0"
    by (cases j) simp_all
  
  lemma iblp1_le:
    assumes "s \<noteq> []"
    shows "iblp1 s j \<le> j"
  proof-\<comment>\<open>It looks like @{method cases}, but it isn't.\<close>
    { 
      assume "j \<ge> length s"
      with \<open>s \<noteq> []\<close> have "iblp1 s j = iblp1 s (length s)"
        by (metis iblp1.elims le_zero_eq list_exhaust_size_eq0 order_mono_setup.refl take_all)
    } moreover {
      fix j
      assume "j \<le> length s"
      then have "iblp1 s j \<le> j"
        apply (cases j)
        apply simp_all
        by (metis eq_imp_le eq_refl intrinsic_border_less len_greater_imp_nonempty length_take linear min.absorb2 nat_in_between_eq(2))
    }
    ultimately show ?thesis
      by (metis dual_order.trans linear)
  qed
  
  lemma iblp1_le': "j > 0 \<Longrightarrow> s \<noteq> [] \<Longrightarrow> iblp1 s j - 1 < j"
  proof -
    assume "s \<noteq> []"
    then have "iblp1 s j \<le> j" by (fact iblp1_le)
    moreover assume "j > 0"
    ultimately show ?thesis
      by linarith
  qed
  
  lemma intrinsic_border_less'': "s \<noteq> [] \<Longrightarrow> iblp1 s j - Suc 0 < length s"
    by (cases j) (simp_all add: intrinsic_border_less')
  
  lemma "p576 et seq":
    assumes
      "s \<noteq> []" and
      assignments:
      "i' = i + (j + 1 - iblp1 s j)"
      "j' = max 0 (iblp1 s j - 1)"
    shows
      sum_no_decrease: "i' + j' \<ge> i + j" (*Todo: When needed? (≙Sinn von S.576?)*) and
      i_increase: "i' > i"
    using assignments by (simp_all add: iblp1_le[OF assms(1), THEN le_imp_less_Suc])
  
  thm longest_common_prefix

subsection\<open>Invariants\<close>
  definition "I_outer t s \<equiv> \<lambda>(i,j,pos).
    (\<forall>i'<i. \<not>is_substring_at s t i') \<and>
    (case pos of None \<Rightarrow> (\<forall>j'<j. t!(i+j') = s!(j')) \<and> j < length s
      | Some p \<Rightarrow> p=i \<and> is_substring_at s t i)"
  text\<open>For the inner loop, we can reuse @{const I_in_nap}.\<close>

subsection\<open>Algorithm\<close>
  text\<open>First, we use the non-evaluable function @{const "iblp1"} directly:}\<close>
  definition "kmp t s \<equiv> do {
    ASSERT (s \<noteq> []);
    let i=0;
    let j=0;
    let pos=None;
    (_,_,pos) \<leftarrow> WHILEIT (I_outer t s) (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
      (j,pos) \<leftarrow> WHILEIT (I_in_nap t s i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
        let j=j+1;
        if j=length s then RETURN (j,Some i) else RETURN (j,None)
      }) (j,pos);
      if pos=None then do {
        ASSERT (j < length s);
        let i = i + j + 1 - iblp1 s j;
        let j = max 0 (iblp1 s j - 1); (*max not necessary*)
        RETURN (i,j,None)
      } else RETURN (i,j,Some i)
    }) (i,j,pos);

    RETURN pos
  }"
  
  lemma substring_substring:
    "\<lbrakk>is_substring_at s1 t i; is_substring_at s2 t (i + length s1)\<rbrakk> \<Longrightarrow> is_substring_at (s1@s2) t i"
    apply (induction s1 t i rule: is_substring_at.induct)
    apply auto
    done
  
  lemma reuse_matches: 
    assumes thi: "0<j" True "j\<le>length s" "\<forall>j'<j. t ! (i + j') = s ! j'"
    shows "\<forall>j'<iblp1 s j - 1. t ! (Suc (i+j) - iblp1 s j + j') = s ! j'"
  proof -
    from iblp1_le'[of j s] thi(1,4) have "\<forall>j'<j. t ! (i + j') = s ! j'" by blast
    with thi have 1: "\<forall>j'<iblp1 s j - 1. t ! (i + j + 1 - iblp1 s j + j') = s ! (j - iblp1 s j + 1 + j')"
      by (smt Groups.ab_semigroup_add_class.add.commute Groups.semigroup_add_class.add.assoc add_diff_cancel_left' iblp1_le le_add_diff_inverse2 len_greater_imp_nonempty less_diff_conv less_or_eq_imp_le)
    have meh: "length (intrinsic_border (take j s)) = iblp1 s j - 1"
      by (metis iblp1.elims diff_add_inverse2 nat_neq_iff thi(1))
    from intrinsic_borderI[of "take j s", unfolded strict_border_def, THEN conjunct1, THEN border_positions]
    have "\<forall>ja<length (intrinsic_border (take j s)). take j s ! ja = take j s ! (min (length s) j - length (intrinsic_border (take j s)) + ja)"
      by (metis border_bot.bot.extremum length_take less_numeral_extra(3) list.size(3) min.absorb2 thi(1) thi(3))
    then have "\<forall>ja<iblp1 s j - 1. take j s ! ja = take j s ! (j - (iblp1 s j - 1) + ja)"
      by (simp add: meh min.absorb2 thi(3))
    then have "\<forall>ja<iblp1 s j - 1. take j s ! ja = take j s ! (j - iblp1 s j + 1 + ja)"
      by (metis One_nat_def Suc_n_minus_m_eq add.right_neutral add_Suc_right iblp1_le le_zero_eq len_greater_imp_nonempty length_greater_0_conv list.size(3) meh thi(1) thi(3) zero_less_diff)
    with thi have 2: "\<forall>j'<iblp1 s j - 1. s ! (j - iblp1 s j + 1 + j') = s ! j'"
      by (smt Groups.ab_semigroup_add_class.add.commute Groups.semigroup_add_class.add.assoc iblp1_le iblp1_le' le_add_diff_inverse2 le_less_trans less_diff_conv less_imp_le_nat nat_add_left_cancel_less nth_take take_eq_Nil)
    from 1 2 have "\<forall>j'<iblp1 s j - 1. t ! (Suc (i+j) - iblp1 s j + j') = s ! j'"
      using Suc_eq_plus1 by presburger
    then show ?thesis.
  qed
  
  lemma shift_safe:
    assumes
      "\<forall>i'<i. \<not>is_substring_at s t i'"
      "t ! (i + j) \<noteq> s ! j"
      "i' < i + (Suc j - iblp1 s j)" and
      [simp]: "j < length s" and
      old_matches: "\<forall>j'<j. t ! (i + j') = s ! j'"
    shows
      "\<not>is_substring_at s t i'"
  proof -
    {
      assume "i'<i" --\<open>Old positions, use invariant.\<close>
      with \<open>\<forall>i'<i. \<not>is_substring_at s t i'\<close> have ?thesis by simp
    } moreover {
      assume "i'=i" --\<open>The mismatch occurred while testing this alignment.\<close>
      with \<open>t!(i+j) \<noteq> s!j\<close> \<open>j<length s\<close> have ?thesis
        using substring_all_positions[of s t i] by auto
    } moreover {
      assume bounds: "i<i'" "i'\<le>i+j-iblp1 s j" --\<open>The skipped positions.\<close>
      from this(1) \<open>i' < i + (Suc j - iblp1 s j)\<close> have "0<j" by linarith
      have important_and_start_and_end: "i + j - i' < length s"
        using assms(4) bounds(1) by linarith
      have "i + j - i' > iblp1 s j - 1"
        by (smt Suc_diff Suc_leI Suc_lessI add_Suc_right add_diff_cancel_left' bounds(1) bounds(2) diff_Suc_Suc diff_diff_cancel diff_le_self diff_less diff_less_mono2 diff_zero dual_order.strict_trans iblp1_j0 le_add2 le_less_trans le_neq_implies_less le_numeral_extra(1) less_imp_diff_less less_imp_le_nat zero_less_diff zero_neq_one)
      then have contradiction: "i + j - i' > length (intrinsic_border (take j s))"
        by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 \<open>0 < j\<close> add_less_cancel_right cancel_comm_monoid_add_class.diff_cancel iblp1.elims length_greater_0_conv less_diff_conv2 less_imp_le_nat list.size(3) nat_neq_iff)
      have [simp]: "i + j - i' < j"
        using \<open>0 < j\<close> bounds(1) by linarith
      have ?thesis
      proof
        assume "is_substring_at s t i'"
        note substring_all_positions[OF this]
        with important_and_start_and_end have a: "\<forall>jj < i+j-i'. t!(i'+jj) = s!jj"
          by simp
        from old_matches have "\<forall>jj < i+j-i'. t!(i'+jj) = s!(i'-i+jj)"
          by (smt Nat.add_diff_assoc2 ab_semigroup_add_class.add.commute add.assoc bounds(1) le_add2 less_diff_conv less_diff_conv2 less_or_eq_imp_le ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
        then have "\<forall>jj < i+j-i'. s!jj = s!(i'-i+jj)"
          using a by auto
        then have "\<forall>jj < i+j-i'. (take j s)!jj = (take j s)!(i'-i+jj)"
          using \<open>i<i'\<close> by auto
        with positions_border[of "i+j-i'" "take j s", simplified]
        have "border (take (i+j-i') s) (take j s)".
        moreover have "take (i+j-i') s \<noteq> take j s"
          by (metis \<open>i + j - i' < j\<close> assms(4) important_and_start_and_end length_take min_simps(2) nat_neq_iff)
        ultimately have "strict_border (take (i+j-i') s) (take j s)" by simp
          note intrinsic_border_greatest[OF this]
        moreover note contradiction
        moreover have "i+j-i' \<le> length s"
          using \<open>i + j - i' < j\<close> \<open>j < length s\<close> by linarith
        ultimately
        show False by simp
      qed
    } moreover {
      assume "i'\<ge>i+(j+1 - iblp1 s j)" --\<open>Future positions, not part of the lemma.\<close>
      with assms(3) have False by simp
    }
    --\<open>Combine the cases\<close>
    ultimately show "\<not>is_substring_at s t i'"
      by fastforce
  qed
  
  lemma kmp_correct: "s \<noteq> []
    \<Longrightarrow> kmp t s \<le> SPEC (\<lambda>None \<Rightarrow>
      (*Todo: equivalent to \<not>sublist s t ?*)
    \<nexists>i. is_substring_at s t i
    | Some i \<Rightarrow>
    is_substring_at s t i \<and> (\<forall>i'<i. \<not>is_substring_at s t i'))"
    unfolding kmp_def I_outer_def I_in_nap_def
    apply (refine_vcg
      WHILEIT_rule[where R="measure (\<lambda>(i,_,pos). length t - i + (if pos = None then 1 else 0))"]
      WHILEIT_rule[where R="measure (\<lambda>(j,_::nat option). length s - j)"]
      )
    apply (vc_solve solve: asm_rl)
    subgoal for i jout j by (metis add_Suc_right all_positions_substring less_antisym)
    subgoal using less_antisym by blast
    subgoal for i jout j i' using shift_safe[of i s t j i'] by simp
    subgoal for i jout j
      apply (cases "j=0")
      apply (simp_all add: reuse_matches intrinsic_border_less'')
      done
    subgoal for i jout j using i_increase[of s _ i j] by fastforce
    subgoal by (auto split: option.splits) (metis substring_lengths add_less_cancel_right leI le_less_trans)
    done
  
  text\<open>We refine the algorithm to compute the @{const iblp1}-values only once at the start:\<close>
  definition computeBordersSpec :: "'a list \<Rightarrow> nat list nres" where
    "computeBordersSpec s \<equiv> ASSERT(s\<noteq>[]) \<then> SPEC (\<lambda>l. length l = length s \<and> (\<forall>i<length s. l!i = iblp1 s i))"
    \<comment>\<open>@{term "i<length s"} is enough, as the @{const ASSERT}-statement right before the @{const iblp1}-usage shows.\<close>
  
  definition "kmp1 t s \<equiv> do {
    ASSERT (s \<noteq> []);
    let i=0;
    let j=0;
    let pos=None;
    borders \<leftarrow> computeBordersSpec s;
    (_,_,pos) \<leftarrow> WHILET (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
      (j,pos) \<leftarrow> WHILET (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
        let j=j+1;
        if j=length s then RETURN (j,Some i) else RETURN (j,None)
      }) (j,pos);
      if pos=None then do {
        ASSERT (j < length borders);
        let i = i + j + 1 - borders!j;
        let j = max 0 (borders!j - 1); (*max not necessary*)
        RETURN (i,j,None)
      } else RETURN (i,j,Some i)
    }) (i,j,pos);

    RETURN pos
  }"
  
  lemma "kmp1 t s \<le> kmp t s"
    apply (rule refine_IdD)
    unfolding kmp1_def kmp_def
    unfolding Let_def computeBordersSpec_def nres_monad_laws
    apply (intro ASSERT_refine_right ASSERT_refine_left)
    apply simp
    apply simp
    apply (rule Refine_Basic.intro_spec_refine)
    apply refine_rcg
    apply refine_dref_type
    apply vc_solve
    done
  
  text\<open>Next, an algorithm that satisfies @{const computeBordersSpec}:\<close>
subsubsection\<open>Computing @{const iblp1}\<close>
  term I_out_na
  definition "I_out_cb s \<equiv> \<lambda>(b,i,j).
    length b = length s \<and>
    (\<forall>jj<j. b!jj = iblp1 s jj) \<and>
    i = b!(j-1) \<and>
    i < j"(*needed?*)
  definition "I_in_cb s bout jout \<equiv> \<lambda>i.
    i < jout \<and> (*needed?*)
    iblp1 s jout \<le> Suc i"
  definition computeBorders :: "'a list \<Rightarrow> nat list nres" where
    "computeBorders s = do {
    ASSERT (s\<noteq>[]);
    let b=[0 ..< length s];(*No longer necessary \<longrightarrow> replace with zeroes?*)
    let i=0;
    let j=1;
    (b,_,_) \<leftarrow> WHILEIT (I_out_cb s) (\<lambda>(b,i,j). j<length s) (\<lambda>(b,i,j). do {
      i \<leftarrow> WHILEIT (I_in_cb s b j) (\<lambda>i. i>0 \<and> s!(i-1) \<noteq> s!(j-1)) (\<lambda>i. do {
      (*Obacht, the \<and> must use short-circuit evaluation
      (otherwise the - actually needs cut-off arithmetic).
      Maybe rewrite beforehand to avoid this?*)
        ASSERT (i < length b);
        i \<leftarrow> mop_list_get b i;
        RETURN i
      }) i;
      let i=i+1;
      ASSERT (j < length b);
      b \<leftarrow> mop_list_set b j i;
      let j=j+1;
      RETURN (b,i,j)
    }) (b,i,j);
    
    RETURN b
  }"
  
  lemma iblp1_1[simp]: "s\<noteq>[] \<Longrightarrow> iblp1 s 1 = 1"
    by (metis One_nat_def Suc_lessI add_gr_0 iblp1.simps(2) iblp1_le leD zero_less_one)
  
  lemma ib1[simp]: "intrinsic_border [z] = []"
    by (metis intrinsic_border_less length_Cons length_ge_1_conv less_Suc0 list.distinct(1) list.size(3))
  
  lemma border_butlast: "border r w \<Longrightarrow> border (butlast r) (butlast w)"
    apply (auto simp: border_def)
     apply (metis butlast_append prefixE prefix_order.eq_refl prefix_prefix prefixeq_butlast)
    apply (metis Sublist.suffix_def append.right_neutral butlast.simps(1) butlast_append)
    done
  
  corollary strict_border_butlast: "r \<noteq> [] \<Longrightarrow> strict_border r w \<Longrightarrow> strict_border (butlast r) (butlast w)"
    unfolding strict_border_altdef by (auto simp: border_butlast less_diff_conv)
  
  lemma border_step: "border r w \<longleftrightarrow> border (r@[w!length r]) (w@[w!length r])"
    apply (auto simp: border_def suffix_def)
    using append_one_prefix prefixE apply fastforce
    using append_prefixD apply blast
    done
  
  lemma intrinsic_border_step: "w \<noteq> [] \<Longrightarrow> intrinsic_border w = r \<Longrightarrow> border (r@[w!length r]) (w@[w!length r])"
    using border_step by (metis ib'_ib intrinsic_border'_def)
  
  lemma intrinsic_border_step': "w \<noteq> [] \<Longrightarrow>  border (intrinsic_border w @[w!length (intrinsic_border w)]) (w@[w!length (intrinsic_border w)])"
    using intrinsic_border_step by blast
  
  lemma ib_butlast[intro]: "length w \<ge> 2 \<Longrightarrow> length (intrinsic_border w) \<le> length (intrinsic_border (butlast w)) + 1"
  proof -
    assume "length w \<ge> 2"
    then have "w \<noteq> []" by auto
    then have "strict_border (intrinsic_border w) w"
      by (fact intrinsic_borderI')
    with \<open>2 \<le> length w\<close> have "strict_border (butlast (intrinsic_border w)) (butlast w)"
      by (metis One_nat_def butlast.simps(1) diff_is_0_eq le_simps(3) length_0_conv length_butlast not_less numeral_2_eq_2 sigh strict_border_butlast)
    then have "length (butlast (intrinsic_border w)) \<le> length (intrinsic_border (butlast w))"
      using intrinsic_border_greatest by blast
    then show ?thesis
      by simp
  qed
  
  corollary iblp1_Suc: "i < length w \<Longrightarrow> iblp1 w (Suc i) \<le> Suc (iblp1 w i)"
    apply (cases i)
     apply (simp_all add: take_Suc0)
      by (metis Suc_eq_plus1 Suc_leI Suc_le_mono Suc_neq_Zero Suc_to_right ib_butlast le_less_linear length_take less_Suc0 min.absorb2 numerals(2) take_minus_one_conv_butlast)
  
  lemma sus: "w \<noteq> [] \<Longrightarrow> length (intrinsic_border (w@[w!length (intrinsic_border w)])) \<le> length (intrinsic_border w) + 1"
    oops
  
  lemma intrinsic_border_step'':
    assumes
      "w \<noteq> []"
      "intrinsic_border w = r"
    shows
      "intrinsic_border (w@[w!length r]) = (r@[w!length r])"
  proof-
    {
      assume "length (intrinsic_border (w @ [w ! length r])) > length r + 1"
      then have "length (intrinsic_border w) > length r"
      proof -
        have "\<not> length (intrinsic_border (w @ [w ! length r])) \<le> length r + 1"
          by (metis \<open>length r + 1 < length (intrinsic_border (w @ [w ! length r]))\<close> leD)
        then show ?thesis
          by (metis (no_types) Suc_leI assms(1) assms(2) butlast_snoc ib_butlast length_Cons length_append length_greater_0_conv less_add_same_cancel2 list.size(3) numeral_2_eq_2)
      qed
      with \<open>intrinsic_border w = r\<close> have False by simp
    }
    then show ?thesis
    proof -
      have f1: "\<forall>as asa. (as = [] \<or> intrinsic_border as \<noteq> asa) \<or> border (asa @ [as ! length asa::'a]) (as @ [as ! length asa])"
        using intrinsic_border_step by blast
      obtain aas :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
        "\<forall>x0 x1. (\<exists>v2. border v2 x0 \<and> v2 \<noteq> x0 \<and> length x1 < length v2) = (border (aas x0 x1) x0 \<and> aas x0 x1 \<noteq> x0 \<and> length x1 < length (aas x0 x1))"
        by moura
      then have f2: "\<forall>as asa. (\<not> intrinsic_border' as asa \<or> border as asa \<and> as \<noteq> asa \<and> (\<forall>asb. \<not> border asb asa \<or> asb = asa \<or> \<not> length as < length asb)) \<and> (intrinsic_border' as asa \<or> \<not> border as asa \<or> as = asa \<or> border (aas asa as) asa \<and> aas asa as \<noteq> asa \<and> length as < length (aas asa as))"
        by (meson intrinsic_border'_def)
      have f3: "1 = length [w ! length r]"
        by auto
      then have "\<not> length (intrinsic_border (w @ [w ! length r])) < length r + 1"
        using f2 f1 by (metis append_is_Nil_conv append_same_eq assms(1) assms(2) ib'_ib length_append)
      then show ?thesis
        using f3 f2 f1 by (metis \<open>length r + 1 < length (intrinsic_border (w @ [w ! length r])) \<Longrightarrow> False\<close> append_is_Nil_conv assms(1) assms(2) border_unique ib'_ib length_append nat_neq_iff)
    qed
  qed
  text "s border[j−1] = s j−1 , so ist border[j] = border[j − 1] + 1"
    
  lemma rule: "\<lbrakk>A \<Longrightarrow> P; \<not>A \<and> B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> A \<or> B \<Longrightarrow> P" by auto
  
  lemma loop_exit: (*or \<dots>_induct ?*)
    assumes
      "i < j"
      "i = 0 \<or> s ! (i - Suc 0) = s ! (j - Suc 0)"
      "j < length s"
      "length b = length s"
      "\<forall>jj<j. b ! jj = iblp1 s jj"
    shows
      "iblp1 s j = Suc i"
  oops
  
  lemma "i < length s \<Longrightarrow> iblp1 s i = i \<Longrightarrow> \<exists>a. take i s = replicate i a"
    (*apply (induction s i rule: above)*)
    oops
  
  thm border_positions
  corollary intrinsic_border_positions: "length (intrinsic_border w) = l
    \<Longrightarrow> \<forall>j<l. w!j = w!(length w - l + j)"
    by (metis add_cancel_left_left border_positions border_step intrinsic_border_step length_0_conv minus_eq)
  
  lemma computeBorders_refine[refine]: "(s,s') \<in> Id \<Longrightarrow> computeBorders s \<le> \<Down> Id (computeBordersSpec s')"
    unfolding computeBordersSpec_def computeBorders_def I_out_cb_def I_in_cb_def
    apply simp
    apply (refine_vcg
      WHILEIT_rule[where R="measure (\<lambda>(b,i,j). length s - j)"]
      WHILEIT_rule[where R="measure id"]\<comment>\<open>\<^term>\<open>i::nat\<close> decreases with every iteration.\<close>
      )
    apply (vc_solve solve: asm_rl)
    subgoal by (metis diff_less lessE less_Suc_eq_0_disj)
    subgoal by (metis Suc_diff_Suc gr_implies_not0 iblp1_Suc less_or_eq_imp_le linorder_neqE_nat minus_nat.diff_0 nz_le_conv_less)
    subgoal by (metis dual_order.strict_trans iblp1_le le_less_trans length_greater_0_conv)
    subgoal for b j i
      proof goal_cases
        case 1
            {
        assume y: "iblp1 s' j > Suc (iblp1 s' i)"
        then obtain jj where yo: "iblp1 s' j = Suc jj" and "jj \<ge> Suc (iblp1 s' i)"
          using Suc_lessE by auto
        then obtain ii  where [simp]: "j = Suc ii"
          by (metis "1"(4) "1"(6) Suc_pred dual_order.strict_trans)
        note yo[simplified]
        note intrinsic_border_positions[OF this, simplified]
        then have yo': "\<forall>j<jj. s'!j = s'!(Suc ii - jj + j)"
          by (smt "1"(2) "1"(4) "1"(6) One_nat_def Suc_to_right \<open>j = Suc ii\<close> add_diff_cancel_left' iblp1_le' less_diff_conv list.size(3) min_less_iff_conj min_pm1 min_simps(2) nat_neq_iff nth_take yo)
        with 1 have "s'!(i - 1) = s'!(j - 1)"
          sorry
      }
      then show ?case
        by (metis "1"(7) One_nat_def le_less_linear)
    qed
    subgoal sorry
    subgoal sorry
    done

subsection\<open>Final refinement\<close>
  text\<open>We replace @{const computeBordersSpec} with @{const computeBorders}\<close>
  definition "kmp2 t s \<equiv> do {
    ASSERT (s \<noteq> []);
    let i=0;
    let j=0;
    let pos=None;
    borders \<leftarrow> computeBorders s;
    (_,_,pos) \<leftarrow> WHILET (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
      (j,pos) \<leftarrow> WHILET (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
        let j=j+1;
        if j=length s then RETURN (j,Some i) else RETURN (j,None)
      }) (j,pos);
      if pos=None then do {
        ASSERT (j < length borders);
        let i = i + j + 1 - borders!j;
        let j = max 0 (borders!j - 1); (*max not necessary*)
        RETURN (i,j,None)
      } else RETURN (i,j,Some i)
    }) (i,j,pos);

    RETURN pos
  }"
  
  text\<open>Using @{thm [source] computeBorders_refine} (it has @{attribute refine}), the proof is trivial:\<close>
  lemma "kmp2 t s \<le> kmp1 t s"
    apply (rule refine_IdD)
    unfolding kmp2_def kmp1_def
    apply refine_rcg
    apply refine_dref_type
    apply vc_solve
    done
  
  lemma alternate_form: "(\<lambda>None \<Rightarrow> \<nexists>i. is_substring_at s t i
      | Some i \<Rightarrow> is_arg_min id (is_substring_at s t) i) =
        (\<lambda>None \<Rightarrow> \<nexists>i. is_substring_at s t i
      | Some i \<Rightarrow> is_substring_at s t i \<and> (\<forall>i'<i. \<not>is_substring_at s t i'))"
    unfolding is_arg_min_def by (auto split: option.split)
  
  lemma "s \<noteq> []
    \<Longrightarrow> kmp t s \<le> SPEC (\<lambda>None \<Rightarrow> \<nexists>i. is_substring_at s t i
      | Some i \<Rightarrow> is_arg_min id (is_substring_at s t) i)"
    unfolding alternate_form by (fact kmp_correct)

(*Todo: Algorithm for the set of all positions. Then: No break-flag needed, and no case distinction in the specification.*)
subsection\<open>@{const computeBorders} using a function instead of a list\<close>
  (*
  no_notation Ref.update ("_ := _" 62)
  definition "computeBorders' s \<equiv> do {
    (*Todo: Assertions*)
    let f=id;
    let i=1;
    let j=2;
    (f,_,_) \<leftarrow> WHILEIT (I_out_cb s f i j) (\<lambda>(f,i,j). j\<le>length s) (\<lambda>(f,i,j). do {
      i \<leftarrow> WHILEIT (I_in_cb s j) (\<lambda>i. i>0 \<and> s!(i-1) \<noteq> s!(j-1)) (\<lambda>i. do {
        let i=f i;
        RETURN i
      }) i;
      let i=i+1;
      let f=f(j:=i);
      RETURN (f,i,j)
    }) (f,i,j);
    
    RETURN f
  }"
  *)
section\<open>Notes and Tests\<close>
  
  term "RETURN (4::nat) = SPEC (\<lambda>x. x=4)" 
  
  definition "test \<equiv> do {
    x \<leftarrow> SPEC (\<lambda>x::nat. x<5);
    y \<leftarrow> SPEC (\<lambda>y. y<10);
    RETURN (x+y)
  }"  
  
  lemma "test \<le> SPEC (\<lambda>x. x<14)"
    unfolding test_def
    apply refine_vcg by auto  
  
  definition "i_test2 x\<^sub>0 \<equiv> \<lambda>(x,s). x\<ge>0 \<and> x\<^sub>0*5 = x*5+s"
  
  definition "test2 x\<^sub>0 \<equiv> do {
    (_,s) \<leftarrow> WHILEIT (i_test2 x\<^sub>0) (\<lambda>(x,s). x>0) (\<lambda>(x,s). do {
      let s = s + 5;
      let x = x - 1;
      RETURN (x,s)
    }) (x\<^sub>0::int,0::int);
    RETURN s
  }"
  
  lemma "x\<ge>0 \<Longrightarrow> test2 x \<le> SPEC (\<lambda>r. r=x*5)"
    unfolding test2_def i_test2_def
    apply (refine_vcg WHILEIT_rule[where R="measure (nat o fst)"])  
    apply auto
    done

section\<open>Examples\<close>
  lemma ex0: "border a '''' \<longleftrightarrow> a\<in>{
    ''''
    }"
    apply (auto simp: border_def slice_char_aux)
    done
    
  lemma ex1: "border a ''a'' \<longleftrightarrow> a\<in>{
    '''',
    ''a''
    }" unfolding border_def apply auto
      by (meson list_se_match(4) suffixE)
  
  lemma ex2: "border a ''aa'' \<longleftrightarrow> a\<in>{
    '''',
    ''a'',
    ''aa''
    }"
    apply (auto simp: border_def)
    apply (smt list.inject prefix_Cons prefix_bot.bot.extremum_uniqueI)
    by (simp add: suffix_ConsI)
  
  lemma ex3: "border a ''aab'' \<longleftrightarrow> a\<in>{
    '''',
    ''aab''
    }"
    apply (auto simp: border_def)
    using ex2 oops
  
  lemma ex7: "border a ''aabaaba'' \<longleftrightarrow> a\<in>{
    '''',
    ''a'',
    ''aaba'',
    ''aabaaba''}"
    apply (auto simp: border_def)
    oops
  
  lemma ex8: "border a ''aabaabaa'' \<longleftrightarrow> a\<in>{
    '''',
    ''a'',
    ''aa'',
    ''aabaa'',
    ''aabaabaa''}"
    apply (auto simp: border_def) oops

end
  (*Todo: rename is_substring_at so that it fits to the new HOL\List.thy. Arg_max is then available, too.*)
