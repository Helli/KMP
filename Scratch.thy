(**)

theory Scratch
  imports Main IICF
begin
  
  term "SPEC (\<lambda>x::nat. x \<in> {4,7,9})"
    
  definition "is_substring_at t s i \<equiv> take (length s) (drop i t) = s"  
    
  term "\<lambda>t s. SPEC (\<lambda>None \<Rightarrow> \<nexists>i. is_substring_at t s i | Some i \<Rightarrow> is_substring_at t s i \<and> (\<forall>j. is_substring_at t s j \<longrightarrow> i\<le>j))"
  
  
  term "RETURN (4::nat) = SPEC (\<lambda>x. x=4)" 
  
  definition "test \<equiv> do {
    x \<leftarrow> SPEC (\<lambda>x::nat. x<5);
    y \<leftarrow> SPEC (\<lambda>y. y<10);
    RETURN (x+y)
  }"  
  
  lemma "test \<le> SPEC (\<lambda>x. x<14)"
    unfolding test_def
    apply refine_vcg by auto  
  
  
  definition "test2 x\<^sub>0 \<equiv> do {
    (_,s) \<leftarrow> WHILEIT (\<lambda>(x,s). x\<ge>0 \<and> x\<^sub>0*5 = x*5+s) (\<lambda>(x,s). x>0) (\<lambda>(x,s). do {
      let s = s + 5;
      let x = x - 1;
      RETURN (x,s)
    }) (x\<^sub>0::int,0::int);
    RETURN s
  }"  
  
  term "measure (nat o fst)"
    
  lemma "x\<ge>0 \<Longrightarrow> test2 x \<le> SPEC (\<lambda>r. r=x*5)"
    unfolding test2_def
    apply (refine_vcg WHILEIT_rule[where R="measure (nat o fst)"])  
    apply auto  
    done
  
  definition border :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where "border s j \<equiv> undefined"    
      
  definition "I_outer \<equiv> \<lambda>(i,j,found). undefined"  
  definition "I_inner iout jout \<equiv> \<lambda>(j,found). undefined"  
    
  definition "kmp t s \<equiv> do {
    let i=0; let j=0;

    (_,_,found) \<leftarrow> WHILEI I_outer (\<lambda>(i,j,found). i\<le>length t - length s \<and> \<not>found) (\<lambda>(i,j,found). do {
      (j,found) \<leftarrow> WHILEI (I_inner i j) (\<lambda>(j,found). t!(i+j) = s!j \<and> \<not>found) (\<lambda>(j,found). do {
        let j=j+1;
        if j=length s then RETURN (j,True) else RETURN (j,False)
      }) (j,found);
      if \<not>found then do {
        let i = i + (j - (border s j - 1));
        let j = max 0 (border s j - 1);
        RETURN (i,j,False)
      } else RETURN (i,j,True)
    }) (i,j,False);

    RETURN found
  }"
      
    
    
  lemma "kmp t s \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<exists>i. is_substring_at t s i))"
    unfolding kmp_def
    apply refine_vcg  
    apply vc_solve  
  
  
  
