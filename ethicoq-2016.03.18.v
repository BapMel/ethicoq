(** * Spinoza: Ethica  *)

(** Ethicoq permet de : 

- vérifier si les démonstrations de Spinoza sont correctes ;

- voir les détours inutiles qu'il réalise, les hypothèses inutiles qu'il
  introduit ;

- corriger ses démonstrations en écrivant noir sur blanc les axiomes
  implicites que l'historien de la philosophie admet aussi implicitement
  que l'auteur,

et ce plus méthodiquement encore que Gueroult, grâce à la rigueur
de Coq. 

Ce système permet également d'expérimenter les changements
d'interprétation, en regardant par exemple si les démonstrations restent
correctes lorsque l'on change le codage d'une des définitions. 

On peut enfin démontrer et vérifier de nouveaux théorèmes spinozistes,
absents de l'Éthique.

Nous espérons ainsi montrer une nouvelle fois, après Gueroult et
Vuillemin, l'apport des sciences formelles à l'histoire structurale de
la philosophie.

*)


(** D'abord un peu de logique. *)

Lemma de_morgan_disj:
  forall P Q: Prop,
    ~(P \/ Q) -> ~P /\ ~Q.

Proof.
  intros P Q npq.
  split; intros p; destruct npq; [left | right]; exact p.
Qed.




(** ----------------------------------------------------------------  *)


(** ** Pars 1: De Deo *)
Module Pars1.


  (** *** Definitiones  *)

  (** Nous aurons besoin d'une notion très générale d'[aliquid]
  (« quelque chose »). Ceci comprendra les substances, attributs et
  modes. C'est le domaine sur lequel on quantifiera. *)

  Variable aliquid: Set.


  (** Pour l'instant, nous ne poserons pas le tiers exclu tant qu'il
  n'est pas nécessaire. Par défaut, la logique utilisée est donc
  intuitionniste. *)



  (** ----------------------------------------------------------------  *)

  (** **** Definitio 1 *)
  (** « Per causam sui intelligo id cujus essentia involvit existentiam
  sive id cujus natura non potest concipi nisi existens. » *)

  (** Il nous faut les prédicats unaires suivants. *)

  Variable causa_sui: aliquid -> Prop.
  Variable ejus_essentia_involvit_existentiam: aliquid -> Prop.
  Variable ejus_natura_potest_concipi_nisi_existens: aliquid -> Prop.

  (** Comme l'indique le [potest] ci-dessus, la logique modale est
  embarquée dans les noms de prédicats, jusqu'à nouvel ordre. Si Spinoza
  a vraiment besoin de raisonnements modaux, nous utiliserons une
  logique modale. *)

  (** Définition 1 (1d1) *)
  Hypothesis Pars1_definitio1: 
    forall a: aliquid, 
      (causa_sui a 
       -> ejus_essentia_involvit_existentiam a 
          /\ ~ejus_natura_potest_concipi_nisi_existens a) 
      /\ 
      (ejus_essentia_involvit_existentiam a 
       \/ ~ejus_natura_potest_concipi_nisi_existens a 
       -> causa_sui a).


  (** **** Definitio 2 *)
  (** « Ea res dicitur in suo genere finita quæ alia ejusdem naturæ
  terminari potest. Exempli gratia corpus dicitur finitum quia aliud
  semper majus concipimus. Sic cogitatio alia cogitatione terminatur. At
  corpus non terminatur cogitatione nec cogitatio corpore. » *)

  Variable terminari_potest: aliquid -> aliquid -> Prop. 
  Variable suo_genere_finita: aliquid -> Prop.

  (** Définition 2 (1d2) *)
  Hypothesis Pars1_definitio2: 
    forall a1: aliquid, 
      suo_genere_finita a1 
      <-> 
      ~(exists a2: aliquid, terminari_potest a1 a2).


  (** **** Definitio 3 *)

  (** « Per substantiam intelligo id quod in se est et per se concipitur
  hoc est id cujus conceptus non indiget conceptu alterius rei a quo
  formari debeat. » *)

  Variable substantia: aliquid -> Prop.

  (** Nous avons besoin de plusieurs nouveaux prédicats unaires ou
  binaires. *)

  Variable existit: aliquid -> Prop.
  Variable existit_in: aliquid -> aliquid -> Prop.
  Variable existit_in_se: aliquid -> Prop.
  Variable existit_in_alio: aliquid -> Prop.

  Variable concipi: aliquid -> Prop.
  Variable concipi_per: aliquid -> aliquid -> Prop.
  Variable concipi_per_se: aliquid -> Prop.
  Variable concipi_per_aliud: aliquid -> Prop.

  (** Les définitions suivantes sont celles d'exister ou d'être conçu
  par soi ou par autre chose. Si Spinoza ne pose pas explicitement ces
  définitions, c'est parce qu'elles sont prises en charge par la langue
  qu'il utilise, à savoir le latin. *)

  Hypothesis existit_in_se_definitio: 
    forall a: aliquid, existit_in_se a <-> existit_in a a.
  Hypothesis existit_in_alio_definitio: 
    forall a1: aliquid, 
      existit_in_alio a1 
      <-> exists a2: aliquid, (a1 <> a2 /\ existit_in a1 a2).

  Hypothesis concipi_per_se_definitio: 
    forall a: aliquid, concipi_per_se a <-> concipi_per a a.
  Hypothesis concipi_per_aliud_definitio: 
    forall a1: aliquid, 
      concipi_per_aliud a1 
      <-> exists a2: aliquid, (a1 <> a2 /\ concipi_per a1 a2).

  (**  Définition 3 (1d3) *)
  Hypothesis Pars1_definitio3:
    forall a: aliquid, 
      (substantia a <-> existit_in_se a) 
      /\ (substantia a <-> concipi_per_se a).


  (** **** Definitio 4 *)

  (** « Per attributum intelligo id quod intellectus de substantia
  percipit tanquam ejusdem essentiam constituens. » *)

  Variable attributum: aliquid -> Prop.
  Variable attributum_substantiæ: aliquid -> aliquid -> Prop.

  Variable cogitat: aliquid -> Prop.
  Variable cognoscit: aliquid -> aliquid -> Prop. 

  (** Définition 4 (1d4) *)
  Hypothesis Pars1_definitio4:
    forall c s: aliquid, 
      cogitat c -> substantia s -> 
      (cognoscit c s 
       <-> exists a: aliquid, (attributum_substantiæ a s /\ cognoscit c a)).


  (** **** Definitio 5 *)
  (** « Per modum intelligo substantiæ affectiones sive id quod in alio
  est, per quod etiam concipitur. » *)

  Variable modum: aliquid -> Prop.
  Variable modum_substantiæ: aliquid -> aliquid -> Prop.

  (* Hypothesis modum_substantiæ_definitio: *)
  (*   forall m s: aliquid, modum_substantiæ m s -> modum m /\ substantia s. *)

  (* Hypothesis Pars1_definitio5: *)
  (*   forall m s: aliquid, *)
  (*     (modum_substantiæ m s -> *)
  (*      modum m /\ substantia s /\ existit_in m s /\ concipi_per m s) *)
  (*     /\ *)
  (*     (modum m /\ substantia s /\ existit_in m s /\ concipi_per m s *)
  (*      -> modum_substantiæ m s). *)

  (** Définition 5 (1d5) *)
  Hypothesis Pars1_definitio5:
    forall m s: aliquid,
      (modum_substantiæ m s 
       <-> 
       modum m /\ substantia s /\ existit_in m s)
      /\
      (modum_substantiæ m s -> concipi_per m s)
      /\
      (modum m <-> existit_in_alio m).

    (* forall m: aliquid, *)
    (*   (modum m <-> *)
    (*    exists s: aliquid,  *)
    (*      (m <> s /\ substantia s /\ existit_in m s /\ concipi_per m s)) *)
    (*   /\  *)
    (*   forall s: aliquid, *)
    (*     (modum_substantiæ m s ->  *)
    (*      modum m /\ substantia s /\ existit_in m s /\ concipi_per m s) *)
    (*     /\ (existit_in m s -> modum_substantiæ m s). *)

  (* Hypothesis Pars1_definitio5: *)
  (*   forall m: aliquid, *)
  (*     (modum m <-> *)
  (*      exists s: aliquid,  *)
  (*        (m <> s /\ substantia s /\ existit_in m s /\ concipi_per m s)) *)
  (*     /\  *)
  (*     forall s: aliquid, *)
  (*       (modum_substantiæ m s ->  *)
  (*        modum m /\ substantia s /\ existit_in m s /\ concipi_per m s) *)
  (*       /\ (existit_in m s -> modum_substantiæ m s). *)


  (* Hypothesis Pars1_definitio5: *)
  (*   forall m s: aliquid, *)
  (*     (modum m -> *)
  (*      exists s: aliquid,  *)
  (*        (substantia s /\ existit_in m s /\ concipi_per m s)) *)
  (*     /\  *)
  (*     (modum_substantiæ m s -> existit_in m s /\ concipi_per m s). *)

  (* Hypothesis Pars1_definitio5: *)
  (*   forall m s: aliquid, *)
  (*     modum m \/ modum_substantiæ m s -> *)
  (*     existit_in m s /\ concipi_per m s. *)


  (** **** Definitio 6 *)
  (** « Per Deum intelligo ens absolute infinitum hoc est substantiam
  constantem infinitis attributis quorum unumquodque æternam et
  infinitam essentiam exprimit. » *)

  Variable absolute_infinitum: aliquid -> Prop.
  Variable infinitis_attributis: aliquid -> Prop.
  Variable est_deus: aliquid -> Prop.

  (** Définition 6 (1d6) *)
  Hypothesis Pars1_definitio6:
    forall a: aliquid,
      est_deus a 
      <-> absolute_infinitum a /\ infinitis_attributis a.


  (** **** Definitio 7 *)
  (** « Ea res libera dicitur quæ ex sola suæ naturæ necessitate existit
  et a se sola ad agendum determinatur. Necessaria autem vel potius
  coacta quæ ab alio determinatur ad existendum et operandum certa ac
  determinata ratione. » *)

  Variable liber: aliquid -> Prop.
  Variable ex_sola_suæ_naturæ_necessitate_existit: aliquid -> Prop.
  Variable a_se_sola_ad_agendum_determinatur: aliquid -> Prop.
  Variable coactus: aliquid -> Prop.

  (** Définition 7 (1d7) *)
  Hypothesis Pars1_definitio7: 
    forall a: aliquid, 
      (liber a ->
       ex_sola_suæ_naturæ_necessitate_existit a /\
       a_se_sola_ad_agendum_determinatur a) 
      /\
      (ex_sola_suæ_naturæ_necessitate_existit a \/
       a_se_sola_ad_agendum_determinatur a
       -> liber a) 
      /\
      (coactus a <-> ~liber a).


  (** **** Definitio 8 *)
  (** « Per æternitatem intelligo ipsam existentiam quatenus ex sola rei
  æternæ definitione necessario sequi concipitur. » *) 

  Variable æternis: aliquid -> Prop. 

  (** Définition 8 (1d8) *)

  (** À remplir ! *)




  (** ----------------------------------------------------------------  *)


  (** *** Axiomata *)

  (** **** Axioma 1 *)
  (** « Omnia quæ sunt vel in se vel in alio sunt. » *)

  (** Axiome 1 (1a1) *)
  Hypothesis Pars1_axioma1:
    forall a: aliquid,
      existit a -> 
      existit_in_se a \/ existit_in_alio a.

  (** Cet axiome pourrait-il être démontré ? Il faudrait pour cela poser
  l'axiome « tout ce qui existe existe dans quelque chose ». Ensuite on
  pourrait dire que cette chose est soit la même, soit une autre (par le
  tiers exclu). On en conclurait que tout ce qui existe existe en soi ou
  en autre chose. *)


  (** **** Axioma 2 *)
  (** « Id quod per aliud non potest concipi, per se concipi debet. » *)

  (** Axiome 2 (1a2) *)
  Hypothesis Pars1_axioma2:
    forall a: aliquid,
      ~concipi_per_aliud a -> 
      concipi_per_se a.

  (** Soulignons le sens de l'implication, qui n'est pas formulée comme
  une équivalence. On ne sait pas si ce qui doit se concevoir par soi ne
  peut être conçu par autre chose. Pourtant, c'est précisément de cette
  réciproque que nous aurons besoin pour démontrer la proposition 2 de
  la première partie. *)



  (** **** Axioma 3 *)
  (** « Ex data causa determinata necessario sequitur effectus et contra
  si nulla detur determinata causa, impossibile est ut effectus
  sequatur. » *)

  Variable causa_determinata: aliquid -> Prop.
  Variable effectus: aliquid -> Prop.
  Variable sequitur: aliquid -> aliquid -> Prop.

  (** Axiome 3 (1a3) *)
  Hypothesis Pars1_axioma3:
    forall a1: aliquid, 
      causa_determinata a1 
      <-> 
      exists a2, (effectus a2 /\ sequitur a1 a2).


  (** **** Axioma 4 *)
  (** « Effectus cognitio a cognitione causæ dependet et eandem
  involvit. » *)

  (** Axiome 4 (1a4) *)
  Hypothesis Pars1_axioma4:
    forall c e: aliquid,
      sequitur c e -> 
      concipi_per e c /\ concipi_per c e.

  (** J'interprète ainsi cet axiome comme « on connaît la cause si et
  seulement si on connaît l'effet. » *)


  (** **** Axioma 5 *)
  (** « Quæ nihil commune cum se invicem habent, etiam per se invicem
  intelligi non possunt sive conceptus unius alterius conceptum non
  involvit. » *)

  Variable habet_aliquid_commune_cum: aliquid -> aliquid -> Prop.


  (** Axiome 5 (1a5) *)
  Hypothesis Pars1_axioma5: 
    forall a1 a2: aliquid,
      ~habet_aliquid_commune_cum a1 a2 -> 
      ~concipi_per a1 a2.

  (* ~(forall c: aliquid, cognoscit c a1 -> cognoscit c a2). *)


  (** **** Axioma 6 *)
  (** « Idea vera debet cum suo ideato convenire. » *)

  (** Axiome 6 (1a6) *)

  (** À faire ! Je regarderai comment Spinoza l'utilise pour savoir
  comment le formuler. *)



  (** **** Axioma 7 *)
  (** « Quicquid ut non existens potest concipi, ejus essentia non
  involvit existentiam. » *)

  (** Axiome 7 (1a7) *)
  Hypothesis Pars1_axioma7:
    forall a: aliquid,
      ejus_natura_potest_concipi_nisi_existens a -> 
      ~ejus_essentia_involvit_existentiam a.



  (** ----------------------------------------------------------------  *)

  (** *** Propositiones  *)

  (** **** Propositio 1 *)
  (** « Substantia prior est natura suis affectionibus. » *)

  (** Dès la première proposition, Spinoza enrichit son vocabulaire. Il
  faut donc définir ce qu'est l'antériorité. Pour cela, je m'appuie sur
  deux prédicats existants : « exister dans » et « être conçu par ». 

  Je définis seulement l'antériorité par une implication. J'avais
  d'abord mis une équivalence, mais Jean-Pascal Anfray m'a dit le 2 juin
  2015 que c'était déjà peut-être trop s'engager métaphysiquement que de
  dire que ce qui est postérieur en nature à quelque chose existe en
  elle ou est conçu par elle. *)

  Variable prior: aliquid -> aliquid -> Prop.

  Hypothesis existit_in_prior:
    forall a1 a2: aliquid, existit_in a2 a1 -> prior a1 a2.

  Hypothesis concipi_per_prior:
    forall a1 a2: aliquid, concipi_per a2 a1 -> prior a1 a2.


  (** Proposition 1 (1p1) *)
  Theorem Pars1_propositio1:
    forall (s m: aliquid), modum_substantiæ m s -> prior s m.

  Proof.
    (** « Demonstratio. Patet ex definitione 3 et 5. » *)

    (** Supposons une substance [s] et un mode [m] qui lui appartient
    ([ms]). *)

    intros s m ms.

    (** Nous montrerons l'antériorité à partir de l'existence en autre
    chose. *) 

    apply existit_in_prior.

    (** Et c'est ici qu'intervient la définition 5 annoncée par Spinoza.
    Elle énonce en effet que le mode existe dans une substance. *)

    apply Pars1_definitio5. 

    (** La démonstration est alors terminée. *)

    exact ms.

  (** Contrairement à ce qu'annonce Spinoza, on n'a pas besoin de la
  définition 3. Il suffit de savoir que le mode dépend de la substance,
  et on n'a pas besoin de savoir que la substance ne dépend de rien.
  Même Gueroult croit que la définition 3 est vraiment utile
  (Gueroult 1968, p. 111) : « étant en soi et conçue par soi, la
  substance ne suppose rien avant elle, contrairement aux modes, qui lui
  sont postérieurs, puisqu'ils ne peuvent qu'être en elle et conçus par
  elle ». *)

  Qed.


  (** **** Propositio 2 *)
  (** « Duæ substantiæ diversa attributa habentes nihil inter se commune
  habent. » *)


  (** Voici la réciproque de l'axiome 2, sans laquelle la proposition
  n'est pas démontrable : ce qui se conçoit par soi ne se conçoit pas
  par autre chose. *)

  Hypothesis Addendum_Pars1_axioma2_reciproce: 
    forall a: aliquid, 
      concipi_per_se a -> 
      ~concipi_per_aliud a.

  (** Il faut aussi préciser que deux choses ont quelque chose en commun
  si et seulement si elles se conçoivent l'une par l'autre. *)

  Hypothesis Addendum_concipi_per_aliquid_commune:
    forall a b: aliquid,
      habet_aliquid_commune_cum a b 
      <-> 
      concipi_per a b.

  (** Proposition 2 (1p2) *)
  Theorem Pars1_propositio2:
    forall s1 s2: aliquid,
      substantia s1 -> 
      substantia s2 -> 
      s1 <> s2 ->
      (forall a: aliquid, 
         attributum_substantiæ a s1 -> ~attributum_substantiæ a s2) ->
      ~habet_aliquid_commune_cum s1 s2.

  Proof.
    (** « Demonstratio. Patet etiam ex definitione 3. Unaquæque enim in
    se debet esse et per se debet concipi sive conceptus unius conceptum
    alterius non involvit. » *) 

    (** Supposons deux substances différentes ([s1] et [s2]) qui n'ont
    aucun attribut en commun ([attr]) mais qui auraient quand même
    quelque chose en commun ([habet]). *)

    intros s1 s2 S1 S2 diff attr habet.

    (** Nous allons parvenir à une contradiction en soutenant à la fois
    qu'une substance se conçoit par autre chose et qu'elle n'est pas
    conçue par autre chose. (Note : sur l'usage des démonstrations par
    l'absurde chez Spinoza, cf. Gueroult 1968, p. 39.) *)

    absurd (concipi_per_aliud s1).

    (** Montrons d'abord qu'une substance ne se conçoit pas par autre
    chose. Pour cela, il faut utiliser la réciproque de l'axiome 2 ainsi
    que la définition 3 ; seule cette dernière est explicitement
    utilisée par Spinoza. *)

    apply Addendum_Pars1_axioma2_reciproce. 
    apply Pars1_definitio3. exact S1.

    (** Montrons maintenant que la substance est conçue par autre chose,
    puisqu'elle est supposée avoir quelque chose en commun avec une
    autre. *)

    apply concipi_per_aliud_definitio. exists s2. split. exact diff. 
    apply Addendum_concipi_per_aliquid_commune. exact habet.

  (** Surprise : l'hypothèse ici nommée [attr] n'est pas utilisée dans
  la démonstration. Gueroult l'a finement observé : « On doit remarquer
  que les attributs différents, par lesquel se distinguent les
  substances, s'ils sont mentionnés dans l'énoncé de la Proposition,
  sont laissés de côté dans la démonstration. Celle-ci se développe
  comme s'il s'agissait simplement d'établir que « deux substances
  différentes n'ont rien de commun entre elles ». » (Gueroult 1968,
  p.~113). *)

Qed.



  (** **** Propositio 3 *)
  (** « Quæ res nihil commune inter se habent, earum una alterius causa
  esse non potest. » *)


  (** Proposition 3 (1p3) *)
  Theorem Pars1_propositio3:
    forall a b: aliquid, ~habet_aliquid_commune_cum a b -> ~sequitur a b.

  Proof.
    (** « Demonstratio. Si nihil commune cum se invicem habent, ergo
    (per axioma 5) nec per se invicem possunt intelligi adeoque (per
    axioma 4) una alterius causa esse non potest. Q.E.D. » *)

    (** Supposons deux choses a et b qui n'ont rien de commun
    ([nhabet]), mais dont la seconde suit pourtant de la première
    ([seq]). *)

    intros a b nhabet seq.

    (** Nous allons montrer une contradiction : on peut démontrer à la
    fois que [a] se conçoit par [b] et qu'il ne se conçoit pas par [b].
    *)

    absurd (concipi_per a b).

    (** Montrons d'abord que [a] ne se conçoit pas par [b]. Cela résulte
    de l'axiome 5, effectivement cité par Spinoza : si, comme on l'a
    supposé, les deux choses n'ont rien de commun, alors elles ne se
    conçoivent pas d'une par l'autre. *)

    apply Pars1_axioma5. exact nhabet.

    (** Montrons pourtant que [a] se conçoit par [b], puisque [b] suit
    de [a]. C'est ce que permet de conclure l'axiome 4, cité par
    Spinoza. *)

    apply Pars1_axioma4. exact seq.

    (** Il n'est donc pas possible d'avoir deux choses dont l'une suive
    de la première sans rien avoir en commun avec elle. *)
  Qed.


  (** **** Propositio 4 *)
  (** « Duæ aut plures res distinctæ vel inter se distinguuntur ex
  diversitate attributorum substantiarum vel ex diversitate earundem
  affectionum. » *)

  Hypothesis Addendum_habet_attributum_aut_modum_commune:
    forall s1 s2: aliquid, 
      substantia s1 -> 
      substantia s2 ->
      ((exists a: aliquid, 
         attributum_substantiæ a s1 /\ attributum_substantiæ a s2) 
         -> habet_aliquid_commune_cum s1 s2) /\
      ((exists a: aliquid, 
         modum_substantiæ a s1 /\ modum_substantiæ a s2) 
         -> habet_aliquid_commune_cum s1 s2).


    (** Montrons que tout ce qui est est soit une substance soit un mode
    (Gueroult 1968, p. 57). Spinoza le fait dans sa démonstration de la
    proposition 4, mais extrayons cette partie de la démonstration car
    elle peut resservir ailleurs. Cet énoncé peut surprendre en raison
    de l'absence des attributs, mais en réalité « l'attribut est
    substance », la différence entre les deux notions n'étant que de
    raison (Gueroult 1968, p. 48). *)

  Lemma omnis_est_substantia_aut_modum: 
    forall a: aliquid, 
      existit a -> 
      substantia a \/ modum a.

  Proof.

    (** Soit [a] une chose qui existe. *)

    intros a existit_a. 

    (** Nous savons par l'axiome 1, cité par Spinoza, que tout ce qui
    existe est en soi ou en autre chose. *)

    destruct Pars1_axioma1 with (a := a) 
      as [a_existit_in_se | a_existit_in_alio]. 
    exact existit_a.

   (** Or si quelque chose existe en soi, alors c'est une substance, en
    vertu de la définition 3, citée par Spinoza. *)

    - left.
      destruct Pars1_definitio3 with (a := a) 
        as [substantia_existit substantia_concipi].
      apply substantia_existit. exact a_existit_in_se.

    (** Et si quelque chose existe en autre chose, alors c'est un mode,
    en vertu de la définition 5, citée par Spinoza. *)

    - right.
      apply Pars1_definitio5. apply a. exact a_existit_in_alio.

  (** La démonstration par Spinoza de cette première étape de la
  proposition 3 est donc correcte. *)

  Qed.



  (** Proposition 4 (1p4) *)
  Theorem Pars1_propositio4:
    forall s1 s2: aliquid, 
      substantia s1 -> 
      substantia s2 -> 
      s1 <> s2 ->
      ~(exists a: aliquid, 
          attributum_substantiæ a s1 /\ attributum_substantiæ a s2)
      /\
      ~(exists m: aliquid, 
          modum_substantiæ m s1 /\ modum_substantiæ m s2).


  (* Reformuler 1d4 pour pouvoir l'utiliser ici ? *)
  (* Idée de la preuve : tout ce qui est est en soi ou en autre chose
  (1a1). Si c'est en soi alors c'est une substance (par 1d3) ou un
  attribut. Si c'est en autre chose alors c'est un mode (par 1d5). Donc
  si deux choses sont différentes, soit elles sont de natures
  différentes (par exemple substance et attribut) et alors c'est trivial
  (mais il faut quand même ajouter l'axiome), soit elles sont de même
  nature et alors soit ce sont deux substances différentes, soit ce sont
  deux attributs différents, soit ce sont deux modes différents. *)

  Proof.
    (** « Omnia quæ sunt vel in se vel in alio sunt (per axioma 1) hoc
    est (per definitiones 3 et 5) extra intellectum nihil datur præter
    substantias earumque affectiones. Nihil ergo extra intellectum datur
    per quod plures res distingui inter se possunt præter substantias
    sive quod idem est (per definitionem 4) earum attributa earumque
    affectiones. Q.E.D. » *)

    (** Supposons deux substances [s1] et [s2] qui sont différentes
    l'une de l'autre ([diff]). *)

    intros s1 s2 S1 S2 diff.

    (** Rappelons que deux substances différentes n'ont rien en commun.
    Cette démonstration est redondante avec une partie de celle de la
    proposition 2 ; il faudrait les factoriser. *)

    assert (non_habent_aliquid_commune: ~habet_aliquid_commune_cum s1 s2).
    intros nhabet.
    absurd (concipi_per_aliud s1).
    apply Addendum_Pars1_axioma2_reciproce. 
    apply Pars1_definitio3. exact S1.
    apply concipi_per_aliud_definitio. exists s2. split. exact diff. 
    apply Addendum_concipi_per_aliquid_commune. exact nhabet.

    (** Montrons maintenant qu'il est impossible que deux substances
    aient un attribut ou un mode commun, car chacune des deux options,
    [habent_attributum_commune] et [habent_modum_commune], mène à une
    contradiction. *)
 
    apply de_morgan_disj.
    intros habent.
    destruct habent as [habent_attributum_commune | habent_modum_commune].

    (** Première option : supposons qu'elles aient en commun un
    attribut [a]. *)

    destruct Addendum_habet_attributum_aut_modum_commune 
    with (s1 := s1) (s2 := s2)
      as [attributum_est_aliquid_commune 
            modum_est_aliquid_commune].
    exact S1. exact S2.
    destruct habent_attributum_commune 
      as [a est_attributum_commune].

    (** Alors elles ont quelque chose en commun. *)

    assert (habent_aliquid_commune: habet_aliquid_commune_cum s1 s2).
    apply attributum_est_aliquid_commune.
    exists a.
    apply est_attributum_commune.

    (** Mais c'est contradictoire avec ce qu'on a établi précédemment.
    *)

    destruct non_habent_aliquid_commune. exact habent_aliquid_commune.

    (** Seconde option : ce qu'elles ont en commun est un mode, qu'on
    appellera [a]. *)

    destruct Addendum_habet_attributum_aut_modum_commune 
    with (s1 := s1) (s2 := s2)
      as [attributum_est_aliquid_commune 
            modum_est_aliquid_commune].
    exact S1. exact S2.
    destruct habent_modum_commune 
      as [a est_modum_commune].

    (** Alors elles ont quelque chose en commun. *)

    assert (habent_aliquid_commune: habet_aliquid_commune_cum s1 s2).
    apply modum_est_aliquid_commune.
    exists a.
    apply est_modum_commune.

    (** Mais c'est contradictoire avec ce qu'on a établi précédemment.
    *)

    destruct non_habent_aliquid_commune. exact habent_aliquid_commune.

  (** Étrangement, la démonstration suivie ici suit une voie très
  différente de celle de Spinoza. On n'a pas besoin d'affirmer que toute
  chose est substance ou mode. En fait, le seul axiome dont on ait
  vraiment besoin est un axiome implicite assez faible : « avoir un
  attribut ou un mode commun, c'est avoir quelque chose de commun ». *)

Qed.



(* démontrer quelques propositions de-ci de-là : 1p24, etc. *)

End Pars1.
