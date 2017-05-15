theory KMP
  imports "$AFP/Refine_Imperative_HOL/IICF/IICF"
begin

section\<open>Definition "substring"\<close>
  definition "is_substring_at' t s i \<equiv> take (length s) (drop i t) = s"  
  
  text\<open>Problem:\<close>
  value "is_substring_at' [5] [] 5"
  value "is_substring_at' [5] [5] 5"
  value "is_substring_at' [] [] 3"
  text\<open>Not very intuitive...\<close>
  
  text\<open>For the moment, we use this instead:\<close>
  fun is_substring_at :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
    t1: "is_substring_at (t#ts) (s#ss) 0 \<longleftrightarrow> t=s \<and> is_substring_at ts ss 0" |
    t2: "is_substring_at (t#ts) ss (Suc i) \<longleftrightarrow> is_substring_at ts ss i" |
    "is_substring_at t [] 0 \<longleftrightarrow> True" |
    "is_substring_at [] _ _ \<longleftrightarrow> False"

  lemmas [code del] = t1 t2
    
  lemma [code]: "is_substring_at (t#ts) ss i \<longleftrightarrow> (if i=0 \<and> ss\<noteq>[] then t=hd ss \<and> is_substring_at ts (tl ss) 0 else is_substring_at ts ss (i-1))"  
    by (cases ss; cases i; auto)
    
  value "is_substring_at [5] [] 5"
  value "is_substring_at [5] [5] 5"
  value "is_substring_at [] [] 3"
  text\<open>Better, I suppose?\<close>
  
  text\<open>For all relevant cases, both definitions agree:\<close>
  lemma "i \<le> length t \<Longrightarrow> is_substring_at t s i \<longleftrightarrow> is_substring_at' t s i"
    unfolding is_substring_at'_def
    by (induction t s i rule: is_substring_at.induct) auto
  
  text\<open>However, the new definition has some reasonable properties:\<close>
  lemma substring_length_s: "is_substring_at t s i \<Longrightarrow> length s \<le> length t"
    apply (induction t s i rule: is_substring_at.induct)
    apply simp_all
    done
  
  lemma substring_i: "is_substring_at t s i \<Longrightarrow> i \<le> length t - length s"
    apply (induction t s i rule: is_substring_at.induct)
    apply (auto simp add: Suc_diff_le substring_length_s)
    done
  
  text\<open>Furthermore, we need:\<close>
  
  lemma substring_step:
    "\<lbrakk>length s + i < length t; is_substring_at t s i; t!(i+length s) = x\<rbrakk> \<Longrightarrow> is_substring_at t (s@[x]) i"
    apply (induction t s i rule: is_substring_at.induct)
    apply auto
    using is_substring_at.elims(3) by fastforce
  
  lemma empty_is_substring: "i \<le> length t \<Longrightarrow> is_substring_at t [] i"
    apply (induction t arbitrary: i)
    apply auto
    using is_substring_at.elims(3) by force
  
  lemma all_positions_substring:
  "\<lbrakk>length s \<le> length t; i \<le> length t - length s; \<forall>j'<length s. t!(i+j') = s!j'\<rbrakk> \<Longrightarrow> is_substring_at t s i"
  proof (induction s rule: rev_induct)
    case Nil
    then show ?case by (simp add: empty_is_substring)
  next
    case (snoc x xs)
    from `length (xs @ [x]) \<le> length t` have "length xs \<le> length t" by simp
    moreover have "i \<le> length t - length xs"
      using snoc.prems(2) by auto
    moreover have "\<forall>j'<length xs. t ! (i + j') = xs ! j'"
      by (metis le_refl length_append less_le_trans nth_append snoc.prems(3) trans_le_add1)
    ultimately have f: "is_substring_at t xs i"
      using snoc.IH by blast
    show ?case
      apply (rule substring_step)
      using snoc.prems(1) snoc.prems(2) apply auto[1]
      apply (fact f)
      by (simp add: snoc.prems(3))
  qed
  
  lemma substring_all_positions:
    "is_substring_at t s i \<Longrightarrow> \<forall>j'<length s. t!(i+j') = s!j'"
    by (induction t s i rule: is_substring_at.induct)
      (auto simp: nth_Cons')
  
  text\<open>Another characterisation:\<close>
  fun slice :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" 
    where
    "slice (x#xs) (Suc n) l = slice xs n l"
  | "slice (x#xs) 0 (Suc l) = x # slice xs 0 l"  
  | "slice _ _ _ = []"  
  
  lemma slice_char_aux: "is_substring_at ts ss 0 \<longleftrightarrow> ss = KMP.slice ts 0 (length ss)"
    apply (induction ts arbitrary: ss)
    subgoal for ss by (cases ss) auto  
    subgoal for a ts ss by (cases ss) auto  
    done    
  
  lemma "\<lbrakk> i<length t \<rbrakk> \<Longrightarrow> is_substring_at t s i \<longleftrightarrow> s = slice t i (length s)"
    apply (induction t s i rule: is_substring_at.induct) 
    apply (auto simp: slice_char_aux)
    done  
  
  (*Todo: fourth alternative: inductive is_substring_at*)

section\<open>Naive algorithm\<close>
subsection\<open>Basic form\<close>
  definition "I_out_na t s \<equiv> \<lambda>(i,j,found).
    \<not>found \<and> j = 0 \<and> (\<forall>i' < i. \<not>is_substring_at t s i')
    \<or> found \<and> is_substring_at t s i"
  definition "I_in_na t s iout (*KMP should need jout, too*) \<equiv> \<lambda>(j,found).
    \<not>found \<and> j < length s \<and> (\<forall>j' < j. t!(iout+j') = s!(j'))
    \<or> found \<and> j = length s \<and> is_substring_at t s iout"
  
  definition "na t s \<equiv> do {
    let i=0;
    let j=0;
    let found=False;
    (_,_,found) \<leftarrow> WHILEIT (I_out_na t s) (\<lambda>(i,j,found). i\<le>length t - length s \<and> \<not>found) (\<lambda>(i,j,found). do {
      (j,found) \<leftarrow> WHILEIT (I_in_na t s i) (\<lambda>(j,found). t!(i+j) = s!j \<and> \<not>found) (\<lambda>(j,found). do {
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
  
  lemma "\<lbrakk>s \<noteq> []; t \<noteq> []; length s \<le> length t\<rbrakk>
    \<Longrightarrow> na t s \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<exists>i. is_substring_at t s i))"
    unfolding na_def I_out_na_def I_in_na_def
    apply (refine_vcg 
          WHILEIT_rule[where R="measure (\<lambda>(i,_,found). (length t - i) + (if found then 0 else 1))"]
          WHILEIT_rule[where R="measure (\<lambda>(j,_::bool). length s - j)"]
          ) 
    apply (vc_solve solve: asm_rl)
    subgoal apply (metis all_positions_substring less_SucE) done
    subgoal using less_Suc_eq apply blast done
    subgoal by (metis less_SucE substring_all_positions)
    subgoal by (meson leI le_less_trans substring_i)
    done
  
  text\<open>These preconditions cannot be removed: If @{term \<open>s = []\<close>} or  @{term \<open>t = []\<close>}, the inner while-condition will access out-of-bound memory. The same can happen if @{term \<open>length t < length s\<close>} (I guess this one could be narrowed down to something like "if t is a proper prefix of s", but that's a bit pointless).\<close>
  (*ToDo: WHILET statt WHILE*)
  
subsection\<open>A variant returning the position\<close>
  definition "I_out_nap t s \<equiv> \<lambda>(i,j,pos).
    (\<forall>i' < i. \<not>is_substring_at t s i') \<and>
    (case pos of None \<Rightarrow> j = 0
      | Some p \<Rightarrow> p=i \<and> is_substring_at t s i)"
  definition "I_in_nap t s iout \<equiv> \<lambda>(j,pos).
    case pos of None \<Rightarrow> j < length s \<and> (\<forall>j' < j. t!(iout+j') = s!(j'))
      | Some p \<Rightarrow> is_substring_at t s iout"

  definition "nap t s \<equiv> do {
    let i=0;
    let j=0;
    let pos=None;
    (_,_,pos) \<leftarrow> WHILEIT (I_out_nap t s) (\<lambda>(i,_,pos). i\<le>length t - length s \<and> pos=None) (\<lambda>(i,j,pos). do {
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
  
  lemma "\<lbrakk>s \<noteq> []; t \<noteq> []; length s \<le> length t\<rbrakk>
    \<Longrightarrow> nap t s \<le> SPEC (\<lambda>None \<Rightarrow> \<nexists>i. is_substring_at t s i | Some i \<Rightarrow> is_substring_at t s i \<and> (\<forall>i'<i. \<not>is_substring_at t s i'))"
    unfolding nap_def I_out_nap_def I_in_nap_def
    apply (refine_vcg
      WHILEIT_rule[where R="measure (\<lambda>(i,_,pos). (length t - i) + (if pos = None then 1 else 0))"]
      WHILEIT_rule[where R="measure (\<lambda>(j,_::nat option). length s - j)"]
      )
    apply (vc_solve solve: asm_rl)
    apply (metis all_positions_substring less_antisym)
    using less_Suc_eq apply blast
    apply (metis less_SucE substring_all_positions)
    by (auto split: option.split intro: leI le_less_trans substring_i)

section\<open>Knuth–Morris–Pratt algorithm\<close>
subsection\<open>Auxiliary definitions\<close>
  definition border :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where "border s j \<equiv> undefined"
  
  (*Todo: Properties*)
  thm longest_common_prefix

subsection\<open>Invariants\<close>
  definition "I_outer \<equiv> \<lambda>(i,j,found). undefined"  
  definition "I_inner iout jout \<equiv> \<lambda>(j,found). undefined"  

subsection\<open>Algorithm\<close>
  definition "kmp t s \<equiv> do {
    let i=0; let j=0;

    (_,_,found) \<leftarrow> WHILEI I_outer (\<lambda>(i,j,found). i\<le>length t - length s \<and> \<not>found) (\<lambda>(i,j,found). do {
      (j,found) \<leftarrow> WHILEI (I_inner i j) (\<lambda>(j,found). t!(i+j) = s!j \<and> \<not>found) (\<lambda>(j,found). do {
        let j=j+1;
        if j=length s then RETURN (j,True) else RETURN (j,False)
      }) (j,found);
      if \<not>found then do {
        let i = i + (j + 1 - border s j);
        let j = max 0 (border s j - 1); (*max not necessary*)
        RETURN (i,j,False)
      } else RETURN (i,j,True)
    }) (i,j,False);

    RETURN found
  }"
        
  lemma substring_substring:
    "\<lbrakk>is_substring_at t s1 i; is_substring_at t s2 (i + length s1)\<rbrakk> \<Longrightarrow> is_substring_at t (s1@s2) i"
    apply (induction t s1 i rule: is_substring_at.induct)
    apply auto
    done

    
  lemma "kmp t s \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<exists>i. is_substring_at t s i))"
    unfolding kmp_def
    apply refine_vcg  
    apply vc_solve
    oops

(*Todo: Algorithm for the set of all positions. Then: No break-flag needed.*)      
section\<open>Notes and Tests\<close>

  term "SPEC (\<lambda>x::nat. x \<in> {4,7,9})"
  
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
  
  term "measure (nat o fst)"
    
  lemma "x\<ge>0 \<Longrightarrow> test2 x \<le> SPEC (\<lambda>r. r=x*5)"
    unfolding test2_def i_test2_def
    apply (refine_vcg WHILEIT_rule[where R="measure (nat o fst)"])  
    apply auto  
    done
    
  value[simp] "\<not>is_substring_at [5::nat] [] 5"
  value[nbe] "\<not>is_substring_at [5::nat] [] 5"
  value[code] "\<not>is_substring_at [5::nat] [] 5"
  lemma "\<not>is_substring_at [5::nat] [] 5"
    by (simp add: eval_nat_numeral(3) numeral_code(2))
  text\<open>What is going on?\<close>
