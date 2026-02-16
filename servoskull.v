(******************************************************************************)
(*                                                                            *)
(*                     Servo Skull Conversion Protocol                        *)
(*                                                                            *)
(*     Formalizing posthumous continuation via servo skull conversion.        *)
(*     Covers pre-mortem cognitive capture, post-mortem processing,           *)
(*     hardware integration, and personality substrate commissioning.         *)
(*                                                                            *)
(*     "Non omnis moriar; multaque pars mei vitabit Libitinam."               *)
(*     - Horace, Odes III.30, 23 BCE                                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 20, 2026                                                 *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Import ListNotations.

Module Authorization.

Inductive AuthorizationPath : Type :=
  | SelfConsent : AuthorizationPath
  | MeritDetermination : AuthorizationPath.

Record ConsentRecord : Type := MkConsentRecord {
  consent_signed : bool;
  consent_witness_count : nat;
  consent_revoked : bool;
  consent_scope_limited : bool
}.

Record MeritRecord : Type := MkMeritRecord {
  merit_years_of_service : nat;
  merit_exceptional_contribution : bool;
  merit_institutional_endorsement : bool;
  merit_posthumous_interval_days : nat
}.

Definition consent_valid (c : ConsentRecord) : bool :=
  consent_signed c && negb (consent_revoked c) && (1 <=? consent_witness_count c).

Definition merit_valid (m : MeritRecord) : bool :=
  merit_exceptional_contribution m && merit_institutional_endorsement m.

Definition authorized (path : AuthorizationPath)
    (c : option ConsentRecord) (m : option MeritRecord) : bool :=
  match path with
  | SelfConsent =>
      match c with
      | Some cr => consent_valid cr
      | None => false
      end
  | MeritDetermination =>
      match m with
      | Some mr => merit_valid mr
      | None => false
      end
  end.

Lemma consent_requires_signature : forall c,
  consent_valid c = true -> consent_signed c = true.
Proof.
  intros c H. unfold consent_valid in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  exact H.
Qed.

Lemma consent_requires_not_revoked : forall c,
  consent_valid c = true -> consent_revoked c = false.
Proof.
  intros c H. unfold consent_valid in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  destruct (consent_revoked c); simpl in H; [discriminate | reflexivity].
Qed.

Lemma revoked_consent_invalid : forall c,
  consent_revoked c = true -> consent_valid c = false.
Proof.
  intros c H. unfold consent_valid.
  rewrite H. simpl.
  rewrite andb_false_r. reflexivity.
Qed.

End Authorization.

Module Subject.

Inductive VitalStatus : Type :=
  | Alive : VitalStatus
  | Deceased : VitalStatus.

Record t : Type := MkSubject {
  subject_id : nat;
  vital_status : VitalStatus;
  age_at_death : option nat;
  hours_since_death : option nat;
  authorization_path : Authorization.AuthorizationPath;
  consent : option Authorization.ConsentRecord;
  merit : option Authorization.MeritRecord
}.

Definition is_deceased (s : t) : bool :=
  match vital_status s with
  | Deceased => true
  | Alive => false
  end.

Definition is_authorized (s : t) : bool :=
  Authorization.authorized (authorization_path s) (consent s) (merit s).

Definition eligible_for_harvest (s : t) : bool :=
  is_deceased s && is_authorized s.

Lemma harvest_requires_death : forall s,
  eligible_for_harvest s = true -> is_deceased s = true.
Proof.
  intros s H. unfold eligible_for_harvest in H.
  apply andb_true_iff in H. destruct H as [H _]. exact H.
Qed.

Lemma harvest_requires_authorization : forall s,
  eligible_for_harvest s = true -> is_authorized s = true.
Proof.
  intros s H. unfold eligible_for_harvest in H.
  apply andb_true_iff in H. destruct H as [_ H]. exact H.
Qed.

Lemma alive_ineligible : forall s,
  vital_status s = Alive -> eligible_for_harvest s = false.
Proof.
  intros s H. unfold eligible_for_harvest, is_deceased. rewrite H.
  reflexivity.
Qed.

End Subject.

Module BehavioralCorpus.

Inductive SourceType : Type :=
  | WrittenWork : SourceType
  | PersonalCorrespondence : SourceType
  | AudioRecording : SourceType
  | VideoRecording : SourceType
  | SocialMedia : SourceType
  | InterviewTranscript : SourceType
  | CourtRecord : SourceType
  | SecondhandAccount : SourceType
  | PsychometricProfile : SourceType
  | JournalDiary : SourceType.

Inductive CollectionTiming : Type :=
  | PreMortem : CollectionTiming
  | PostMortem : CollectionTiming.

Record CorpusEntry : Type := MkCorpusEntry {
  entry_source_type : SourceType;
  entry_timing : CollectionTiming;
  entry_size_bytes : nat;
  entry_verified : bool;
  entry_year : nat
}.

Record t : Type := MkCorpus {
  entries : list CorpusEntry;
  total_hours_audio : nat;
  total_hours_video : nat;
  total_words_text : nat;
  distinct_source_count : nat
}.

Definition entry_count (c : t) : nat := length (entries c).

Definition has_audio (c : t) : bool := 1 <=? total_hours_audio c.

Definition has_video (c : t) : bool := 1 <=? total_hours_video c.

Definition has_text (c : t) : bool := 1000 <=? total_words_text c.

Definition multi_source (c : t) : bool := 3 <=? distinct_source_count c.

Definition corpus_sufficient (c : t) : bool :=
  (1 <=? entry_count c) &&
  (has_audio c || has_text c) &&
  multi_source c.

Definition empty : t :=
  MkCorpus [] 0 0 0 0.

Lemma empty_corpus_insufficient : corpus_sufficient empty = false.
Proof. reflexivity. Qed.

Lemma sufficient_requires_entries : forall c,
  corpus_sufficient c = true -> 1 <= entry_count c.
Proof.
  intros c H. unfold corpus_sufficient in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.leb_le in H. exact H.
Qed.

Lemma sufficient_requires_multi_source : forall c,
  corpus_sufficient c = true -> 3 <= distinct_source_count c.
Proof.
  intros c H. unfold corpus_sufficient in H.
  apply andb_true_iff in H. destruct H as [_ H].
  apply Nat.leb_le in H. exact H.
Qed.

End BehavioralCorpus.

Module CranialHarvest.

(* Instruments *)

Inductive ScalpelBlade : Type :=
  | Blade10 : ScalpelBlade
  | Blade15 : ScalpelBlade
  | Blade20 : ScalpelBlade
  | Blade22 : ScalpelBlade.

Inductive Instrument : Type :=
  | Scalpel : ScalpelBlade -> Instrument
  | PeriostealElevator_Freer : Instrument
  | PeriostealElevator_Molt : Instrument
  | PeriostealElevator_Langenbeck : Instrument
  | Rongeur_Leksell : Instrument
  | Rongeur_Kerrison : Instrument
  | OscillatingSaw_Stryker : Instrument
  | GigliSaw : Instrument
  | Osteotome_Straight : Instrument
  | Osteotome_Curved : Instrument
  | Chisel_Flat : Instrument
  | Mallet : Instrument
  | BoneCurette_Small : Instrument
  | BoneCurette_Large : Instrument
  | DissectingScissors_Mayo : Instrument
  | DissectingScissors_Metzenbaum : Instrument
  | TissueForceps_Adson : Instrument
  | TissueForceps_DeBakey : Instrument
  | TissueForceps_Rat_Tooth : Instrument
  | BoneForceps_Reduction : Instrument
  | Retractor_Weitlaner : Instrument
  | Retractor_Gelpi : Instrument
  | SuctionTip_Yankauer : Instrument
  | SuctionTip_Frazier : Instrument
  | Electrocautery_Bovie : Instrument
  | DuralHook : Instrument
  | NerveHook : Instrument
  | PituitaryCurette : Instrument
  | Rugine : Instrument
  | CranialPerforator_Hudson : Instrument.

(* Individual cranial bones — each tracked for integrity *)

Inductive CranialBone : Type :=
  | Frontal : CranialBone
  | ParietalLeft : CranialBone
  | ParietalRight : CranialBone
  | Occipital : CranialBone
  | TemporalLeft : CranialBone
  | TemporalRight : CranialBone
  | Sphenoid : CranialBone
  | Ethmoid : CranialBone
  | MaxillaLeft : CranialBone
  | MaxillaRight : CranialBone
  | ZygomaticLeft : CranialBone
  | ZygomaticRight : CranialBone
  | NasalLeft : CranialBone
  | NasalRight : CranialBone
  | LacrimalLeft : CranialBone
  | LacrimalRight : CranialBone
  | PalatineLeft : CranialBone
  | PalatineRight : CranialBone
  | InferiorConchaLeft : CranialBone
  | InferiorConchaRight : CranialBone
  | Vomer : CranialBone
  | Mandible : CranialBone.

(* Cranial sutures — each assessed for integrity post-extraction *)

Inductive CranialSuture : Type :=
  | Coronal : CranialSuture
  | Sagittal : CranialSuture
  | Lambdoid : CranialSuture
  | Squamosal_Left : CranialSuture
  | Squamosal_Right : CranialSuture
  | Metopic : CranialSuture
  | Sphenofrontal_Left : CranialSuture
  | Sphenofrontal_Right : CranialSuture
  | Sphenoparietal_Left : CranialSuture
  | Sphenoparietal_Right : CranialSuture
  | Sphenosquamosal_Left : CranialSuture
  | Sphenosquamosal_Right : CranialSuture
  | Parietomastoid_Left : CranialSuture
  | Parietomastoid_Right : CranialSuture
  | Occipitomastoid_Left : CranialSuture
  | Occipitomastoid_Right : CranialSuture
  | Frontozygomatic_Left : CranialSuture
  | Frontozygomatic_Right : CranialSuture
  | Zygomaticomaxillary_Left : CranialSuture
  | Zygomaticomaxillary_Right : CranialSuture
  | Intermaxillary : CranialSuture
  | Internasal : CranialSuture
  | Frontonasal : CranialSuture
  | Nasomaxillary_Left : CranialSuture
  | Nasomaxillary_Right : CranialSuture
  | Frontomaxillary_Left : CranialSuture
  | Frontomaxillary_Right : CranialSuture
  | Palatomaxillary_Left : CranialSuture
  | Palatomaxillary_Right : CranialSuture
  | Temporozygomatic_Left : CranialSuture
  | Temporozygomatic_Right : CranialSuture.

(* Cranial foramina — each must be preserved for cable routing *)

Inductive Foramen : Type :=
  | ForamenMagnum : Foramen
  | OpticCanal_Left : Foramen
  | OpticCanal_Right : Foramen
  | SuperiorOrbitalFissure_Left : Foramen
  | SuperiorOrbitalFissure_Right : Foramen
  | InferiorOrbitalFissure_Left : Foramen
  | InferiorOrbitalFissure_Right : Foramen
  | ForamenRotundum_Left : Foramen
  | ForamenRotundum_Right : Foramen
  | ForamenOvale_Left : Foramen
  | ForamenOvale_Right : Foramen
  | ForamenSpinosum_Left : Foramen
  | ForamenSpinosum_Right : Foramen
  | ForamenLacerum_Left : Foramen
  | ForamenLacerum_Right : Foramen
  | InternalAcousticMeatus_Left : Foramen
  | InternalAcousticMeatus_Right : Foramen
  | ExternalAcousticMeatus_Left : Foramen
  | ExternalAcousticMeatus_Right : Foramen
  | JugularForamen_Left : Foramen
  | JugularForamen_Right : Foramen
  | HypoglossalCanal_Left : Foramen
  | HypoglossalCanal_Right : Foramen
  | CarotidCanal_Left : Foramen
  | CarotidCanal_Right : Foramen
  | StylemastoidForamen_Left : Foramen
  | StylemastoidForamen_Right : Foramen
  | SupraorbitalForamen_Left : Foramen
  | SupraorbitalForamen_Right : Foramen
  | InfraorbitalForamen_Left : Foramen
  | InfraorbitalForamen_Right : Foramen
  | MentalForamen_Left : Foramen
  | MentalForamen_Right : Foramen
  | MandibularForamen_Left : Foramen
  | MandibularForamen_Right : Foramen
  | IncisiveForamen : Foramen
  | GreaterPalatineForamen_Left : Foramen
  | GreaterPalatineForamen_Right : Foramen
  | LesserPalatineForamen_Left : Foramen
  | LesserPalatineForamen_Right : Foramen
  | ForamenCecum : Foramen
  | CribriformForamina : Foramen.

(* Muscles requiring dissection from skull *)

Inductive CranialMuscle : Type :=
  | Temporalis_Left : CranialMuscle
  | Temporalis_Right : CranialMuscle
  | Masseter_Left : CranialMuscle
  | Masseter_Right : CranialMuscle
  | LateralPterygoid_Left : CranialMuscle
  | LateralPterygoid_Right : CranialMuscle
  | MedialPterygoid_Left : CranialMuscle
  | MedialPterygoid_Right : CranialMuscle
  | Buccinator_Left : CranialMuscle
  | Buccinator_Right : CranialMuscle
  | Orbicularis_Oculi_Left : CranialMuscle
  | Orbicularis_Oculi_Right : CranialMuscle
  | Orbicularis_Oris : CranialMuscle
  | Frontalis : CranialMuscle
  | Occipitalis : CranialMuscle
  | Procerus : CranialMuscle
  | Nasalis_Left : CranialMuscle
  | Nasalis_Right : CranialMuscle
  | Corrugator_Supercilii_Left : CranialMuscle
  | Corrugator_Supercilii_Right : CranialMuscle
  | Levator_Labii_Left : CranialMuscle
  | Levator_Labii_Right : CranialMuscle
  | Zygomaticus_Major_Left : CranialMuscle
  | Zygomaticus_Major_Right : CranialMuscle
  | Zygomaticus_Minor_Left : CranialMuscle
  | Zygomaticus_Minor_Right : CranialMuscle
  | Depressor_Anguli_Oris_Left : CranialMuscle
  | Depressor_Anguli_Oris_Right : CranialMuscle
  | Mentalis_Left : CranialMuscle
  | Mentalis_Right : CranialMuscle
  | Platysma_Left : CranialMuscle
  | Platysma_Right : CranialMuscle
  | Digastric_Anterior_Left : CranialMuscle
  | Digastric_Anterior_Right : CranialMuscle
  | Digastric_Posterior_Left : CranialMuscle
  | Digastric_Posterior_Right : CranialMuscle
  | Mylohyoid_Left : CranialMuscle
  | Mylohyoid_Right : CranialMuscle
  | Geniohyoid_Left : CranialMuscle
  | Geniohyoid_Right : CranialMuscle
  | Stylohyoid_Left : CranialMuscle
  | Stylohyoid_Right : CranialMuscle
  | Sternocleidomastoid_Left : CranialMuscle
  | Sternocleidomastoid_Right : CranialMuscle
  | Splenius_Capitis_Left : CranialMuscle
  | Splenius_Capitis_Right : CranialMuscle
  | Semispinalis_Capitis_Left : CranialMuscle
  | Semispinalis_Capitis_Right : CranialMuscle
  | Longissimus_Capitis_Left : CranialMuscle
  | Longissimus_Capitis_Right : CranialMuscle
  | Rectus_Capitis_Posterior_Major_Left : CranialMuscle
  | Rectus_Capitis_Posterior_Major_Right : CranialMuscle
  | Rectus_Capitis_Posterior_Minor_Left : CranialMuscle
  | Rectus_Capitis_Posterior_Minor_Right : CranialMuscle
  | Obliquus_Capitis_Superior_Left : CranialMuscle
  | Obliquus_Capitis_Superior_Right : CranialMuscle
  | Rectus_Capitis_Lateralis_Left : CranialMuscle
  | Rectus_Capitis_Lateralis_Right : CranialMuscle
  | Rectus_Capitis_Anterior_Left : CranialMuscle
  | Rectus_Capitis_Anterior_Right : CranialMuscle
  | Longus_Capitis_Left : CranialMuscle
  | Longus_Capitis_Right : CranialMuscle.

(* Cranial nerves transected at skull base *)

Inductive CranialNerve : Type :=
  | CN_I_Olfactory_Left : CranialNerve
  | CN_I_Olfactory_Right : CranialNerve
  | CN_II_Optic_Left : CranialNerve
  | CN_II_Optic_Right : CranialNerve
  | CN_III_Oculomotor_Left : CranialNerve
  | CN_III_Oculomotor_Right : CranialNerve
  | CN_IV_Trochlear_Left : CranialNerve
  | CN_IV_Trochlear_Right : CranialNerve
  | CN_V1_Ophthalmic_Left : CranialNerve
  | CN_V1_Ophthalmic_Right : CranialNerve
  | CN_V2_Maxillary_Left : CranialNerve
  | CN_V2_Maxillary_Right : CranialNerve
  | CN_V3_Mandibular_Left : CranialNerve
  | CN_V3_Mandibular_Right : CranialNerve
  | CN_VI_Abducens_Left : CranialNerve
  | CN_VI_Abducens_Right : CranialNerve
  | CN_VII_Facial_Left : CranialNerve
  | CN_VII_Facial_Right : CranialNerve
  | CN_VIII_Vestibulocochlear_Left : CranialNerve
  | CN_VIII_Vestibulocochlear_Right : CranialNerve
  | CN_IX_Glossopharyngeal_Left : CranialNerve
  | CN_IX_Glossopharyngeal_Right : CranialNerve
  | CN_X_Vagus_Left : CranialNerve
  | CN_X_Vagus_Right : CranialNerve
  | CN_XI_Accessory_Left : CranialNerve
  | CN_XI_Accessory_Right : CranialNerve
  | CN_XII_Hypoglossal_Left : CranialNerve
  | CN_XII_Hypoglossal_Right : CranialNerve.

(* Blood vessels severed during harvest *)

Inductive CranialVessel : Type :=
  | InternalCarotid_Left : CranialVessel
  | InternalCarotid_Right : CranialVessel
  | VertebralArtery_Left : CranialVessel
  | VertebralArtery_Right : CranialVessel
  | BasilarArtery : CranialVessel
  | InternalJugular_Left : CranialVessel
  | InternalJugular_Right : CranialVessel
  | ExternalJugular_Left : CranialVessel
  | ExternalJugular_Right : CranialVessel
  | SuperficialTemporal_Left : CranialVessel
  | SuperficialTemporal_Right : CranialVessel
  | Facial_Artery_Left : CranialVessel
  | Facial_Artery_Right : CranialVessel
  | Occipital_Artery_Left : CranialVessel
  | Occipital_Artery_Right : CranialVessel
  | MiddleMeningeal_Left : CranialVessel
  | MiddleMeningeal_Right : CranialVessel
  | SuperiorSagittalSinus : CranialVessel
  | InferiorSagittalSinus : CranialVessel
  | StraightSinus : CranialVessel
  | TransverseSinus_Left : CranialVessel
  | TransverseSinus_Right : CranialVessel
  | SigmoidSinus_Left : CranialVessel
  | SigmoidSinus_Right : CranialVessel
  | CavernousSinus_Left : CranialVessel
  | CavernousSinus_Right : CranialVessel.

(* Intracranial contents requiring removal *)

Inductive IntracranialContent : Type :=
  | CerebralHemisphere_Left : IntracranialContent
  | CerebralHemisphere_Right : IntracranialContent
  | Cerebellum_Left : IntracranialContent
  | Cerebellum_Right : IntracranialContent
  | Brainstem_Midbrain : IntracranialContent
  | Brainstem_Pons : IntracranialContent
  | Brainstem_Medulla : IntracranialContent
  | PituitaryGland : IntracranialContent
  | FalxCerebri : IntracranialContent
  | TentoriumCerebelli : IntracranialContent
  | FalxCerebelli : IntracranialContent
  | DuraMater_Convexity : IntracranialContent
  | DuraMater_SkullBase : IntracranialContent
  | ArachnoidMater : IntracranialContent
  | PiaMater : IntracranialContent
  | ChoroidPlexus : IntracranialContent
  | Cerebrospinal_Fluid : IntracranialContent
  | Tentorium_Free_Edge : IntracranialContent
  | DiaphragmaSellae : IntracranialContent.

(* Orbital contents requiring evisceration *)

Inductive OrbitalContent : Type :=
  | Globe_Left : OrbitalContent
  | Globe_Right : OrbitalContent
  | OrbitalFat_Left : OrbitalContent
  | OrbitalFat_Right : OrbitalContent
  | LacrimalGland_Left : OrbitalContent
  | LacrimalGland_Right : OrbitalContent
  | ExtraocularMuscles_Left : OrbitalContent
  | ExtraocularMuscles_Right : OrbitalContent
  | Periorbita_Left : OrbitalContent
  | Periorbita_Right : OrbitalContent
  | NasolacrimalDuct_Left : OrbitalContent
  | NasolacrimalDuct_Right : OrbitalContent.

(* Nasal and oral cavity contents *)

Inductive NasalOralContent : Type :=
  | NasalSeptumCartilage : NasalOralContent
  | InferiorTurbinate_Left : NasalOralContent
  | InferiorTurbinate_Right : NasalOralContent
  | MiddleTurbinate_Left : NasalOralContent
  | MiddleTurbinate_Right : NasalOralContent
  | SuperiorTurbinate_Left : NasalOralContent
  | SuperiorTurbinate_Right : NasalOralContent
  | NasalMucosa : NasalOralContent
  | OralMucosa : NasalOralContent
  | Tongue : NasalOralContent
  | SoftPalate : NasalOralContent
  | HardPalateMucosa : NasalOralContent
  | Gingiva : NasalOralContent
  | Tonsils : NasalOralContent
  | SalivaryGlands : NasalOralContent
  | Teeth : NasalOralContent.

(* Incision and approach *)

Inductive ScalpIncision : Type :=
  | CircumferentialCervical : ScalpIncision
  | BicorocalReflection : ScalpIncision
  | PosteriorMidlineY : ScalpIncision.

Inductive CervicalApproach : Type :=
  | AnteriorCervical : CervicalApproach
  | PosteriorCervical : CervicalApproach
  | CircumferentialCervical_Approach : CervicalApproach.

Inductive DisarticulationLevel : Type :=
  | AtlantoOccipital_C0C1 : DisarticulationLevel
  | AxisLevel_C1C2 : DisarticulationLevel.

Inductive DisarticulationStructure : Type :=
  | TectorialMembrane : DisarticulationStructure
  | CruciateLigament : DisarticulationStructure
  | AlarLigament_Left : DisarticulationStructure
  | AlarLigament_Right : DisarticulationStructure
  | ApicalLigament : DisarticulationStructure
  | AnteriorAtlantoOccipitalMembrane : DisarticulationStructure
  | PosteriorAtlantoOccipitalMembrane : DisarticulationStructure
  | AtlantoOccipitalCapsule_Left : DisarticulationStructure
  | AtlantoOccipitalCapsule_Right : DisarticulationStructure
  | SpinalCord : DisarticulationStructure
  | VertebralArtery_LeftAtC1 : DisarticulationStructure
  | VertebralArtery_RightAtC1 : DisarticulationStructure.

(* Environment *)

Record HarvestEnvironment : Type := MkHarvestEnv {
  facility_licensed : bool;
  anatomist_credentialed : bool;
  assistant_present : bool;
  refrigeration_available : bool;
  sterile_field : bool;
  adequate_lighting : bool;
  suction_available : bool;
  hours_postmortem_at_start : nat;
  ambient_temperature_c_x10 : nat;
  body_refrigerated_since_death : bool;
  decomposition_grade : nat
}.

(* Decomposition: 0=fresh, 1=early autolysis, 2=bloat, 3=active decay *)

Definition environment_acceptable (e : HarvestEnvironment) : bool :=
  facility_licensed e &&
  anatomist_credentialed e &&
  assistant_present e &&
  refrigeration_available e &&
  sterile_field e &&
  adequate_lighting e &&
  suction_available e &&
  (hours_postmortem_at_start e <=? 72) &&
  (decomposition_grade e <=? 1).

(* The full procedure record *)

Record HarvestProcedure : Type := MkHarvestProcedure {
  (* Approach *)
  scalp_incision : ScalpIncision;
  cervical_approach : CervicalApproach;
  disarticulation_level : DisarticulationLevel;

  (* Structures divided at disarticulation *)
  disarticulation_structures_divided : list DisarticulationStructure;

  (* Muscles dissected from bone *)
  muscles_dissected : list CranialMuscle;

  (* Nerves transected *)
  nerves_transected : list CranialNerve;

  (* Vessels ligated or divided *)
  vessels_divided : list CranialVessel;

  (* Intracranial contents removed *)
  intracranial_contents_removed : list IntracranialContent;

  (* Orbital contents eviscerated *)
  orbital_contents_removed : list OrbitalContent;

  (* Nasal and oral contents removed *)
  nasal_oral_contents_removed : list NasalOralContent;

  (* Bone integrity *)
  bones_intact : list CranialBone;
  bones_damaged : list CranialBone;
  sutures_intact : list CranialSuture;
  sutures_damaged : list CranialSuture;
  foramina_patent : list Foramen;
  foramina_occluded : list Foramen;

  (* Mandible *)
  mandible_retained : bool;
  tmj_disarticulated_cleanly : bool;
  condyles_intact : bool;
  coronoid_processes_intact : bool;

  (* Teeth *)
  teeth_retained : bool;
  teeth_count : nat;

  (* Instruments used *)
  instruments_used : list Instrument;

  (* Metrics *)
  procedure_duration_minutes : nat;
  estimated_blood_loss_mL : nat
}.

(* Completeness checks *)

Definition minimum_muscles_dissected : nat := 62.
Definition minimum_nerves_transected : nat := 24.
Definition minimum_vessels_divided : nat := 20.
Definition minimum_intracranial_removed : nat := 19.
Definition minimum_orbital_removed : nat := 12.
Definition minimum_nasal_oral_removed : nat := 14.
Definition minimum_disarticulation_structures : nat := 10.
Definition minimum_bones_intact : nat := 20.
Definition minimum_foramina_patent : nat := 30.
Definition minimum_sutures_intact : nat := 25.

Definition muscles_complete (p : HarvestProcedure) : bool :=
  minimum_muscles_dissected <=? length (muscles_dissected p).

Definition nerves_complete (p : HarvestProcedure) : bool :=
  minimum_nerves_transected <=? length (nerves_transected p).

Definition vessels_complete (p : HarvestProcedure) : bool :=
  minimum_vessels_divided <=? length (vessels_divided p).

Definition intracranial_complete (p : HarvestProcedure) : bool :=
  minimum_intracranial_removed <=? length (intracranial_contents_removed p).

Definition orbital_complete (p : HarvestProcedure) : bool :=
  minimum_orbital_removed <=? length (orbital_contents_removed p).

Definition nasal_oral_complete (p : HarvestProcedure) : bool :=
  minimum_nasal_oral_removed <=? length (nasal_oral_contents_removed p).

Definition disarticulation_complete (p : HarvestProcedure) : bool :=
  minimum_disarticulation_structures <=? length (disarticulation_structures_divided p).

Definition bone_integrity (p : HarvestProcedure) : bool :=
  (minimum_bones_intact <=? length (bones_intact p)) &&
  (length (bones_damaged p) =? 0).

Definition foramina_integrity (p : HarvestProcedure) : bool :=
  (minimum_foramina_patent <=? length (foramina_patent p)) &&
  (length (foramina_occluded p) <=? 2).

Definition suture_integrity (p : HarvestProcedure) : bool :=
  minimum_sutures_intact <=? length (sutures_intact p).

Definition mandible_integrity (p : HarvestProcedure) : bool :=
  if mandible_retained p then
    tmj_disarticulated_cleanly p &&
    condyles_intact p &&
    coronoid_processes_intact p
  else true.

Definition structural_integrity (p : HarvestProcedure) : bool :=
  bone_integrity p &&
  foramina_integrity p &&
  suture_integrity p &&
  mandible_integrity p.

Definition dissection_complete (p : HarvestProcedure) : bool :=
  muscles_complete p &&
  nerves_complete p &&
  vessels_complete p &&
  intracranial_complete p &&
  orbital_complete p &&
  nasal_oral_complete p &&
  disarticulation_complete p.

Definition harvest_successful (e : HarvestEnvironment)
    (p : HarvestProcedure) : bool :=
  environment_acceptable e &&
  dissection_complete p &&
  structural_integrity p.

Lemma env_acc_elim : forall e,
  environment_acceptable e = true ->
  facility_licensed e = true /\
  anatomist_credentialed e = true /\
  assistant_present e = true /\
  refrigeration_available e = true /\
  sterile_field e = true /\
  adequate_lighting e = true /\
  suction_available e = true /\
  hours_postmortem_at_start e <= 72 /\
  decomposition_grade e <= 1.
Proof.
  intros e H. unfold environment_acceptable in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  repeat split; try assumption;
  try (apply Nat.leb_le; assumption).
Qed.

Lemma dissection_elim : forall p,
  dissection_complete p = true ->
  62 <= length (muscles_dissected p) /\
  24 <= length (nerves_transected p) /\
  20 <= length (vessels_divided p) /\
  19 <= length (intracranial_contents_removed p) /\
  12 <= length (orbital_contents_removed p) /\
  14 <= length (nasal_oral_contents_removed p) /\
  10 <= length (disarticulation_structures_divided p).
Proof.
  intros p H. unfold dissection_complete in H.
  unfold muscles_complete, nerves_complete, vessels_complete,
    intracranial_complete, orbital_complete, nasal_oral_complete,
    disarticulation_complete in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  repeat split; apply Nat.leb_le; assumption.
Qed.

Lemma harvest_requires_licensed_facility : forall e p,
  harvest_successful e p = true -> facility_licensed e = true.
Proof.
  intros e p H. unfold harvest_successful in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply env_acc_elim in H. destruct H as [H _]. exact H.
Qed.

Lemma harvest_requires_no_decomposition : forall e p,
  harvest_successful e p = true -> decomposition_grade e <= 1.
Proof.
  intros e p H. unfold harvest_successful in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply env_acc_elim in H.
  destruct H as [_ [_ [_ [_ [_ [_ [_ [_ H]]]]]]]]. exact H.
Qed.

Lemma harvest_requires_all_muscles : forall e p,
  harvest_successful e p = true -> 62 <= length (muscles_dissected p).
Proof.
  intros e p H. unfold harvest_successful in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  apply dissection_elim in H. destruct H as [H _]. exact H.
Qed.

Lemma harvest_requires_all_nerves : forall e p,
  harvest_successful e p = true -> 24 <= length (nerves_transected p).
Proof.
  intros e p H. unfold harvest_successful in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  apply dissection_elim in H.
  destruct H as [_ [H _]]. exact H.
Qed.

Lemma harvest_requires_foramina_patent : forall e p,
  harvest_successful e p = true -> 30 <= length (foramina_patent p).
Proof.
  intros e p H. unfold harvest_successful in H.
  apply andb_true_iff in H. destruct H as [_ H].
  unfold structural_integrity in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [_ H].
  unfold foramina_integrity in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.leb_le in H. exact H.
Qed.

Lemma harvest_within_72_hours : forall e p,
  harvest_successful e p = true -> hours_postmortem_at_start e <= 72.
Proof.
  intros e p H. unfold harvest_successful in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply env_acc_elim in H.
  destruct H as [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]. exact H.
Qed.

End CranialHarvest.

Module Defleshing.

Inductive DefleshingMethod : Type :=
  | WaterMaceration : DefleshingMethod
  | EnzymaticMaceration_Papain : DefleshingMethod
  | EnzymaticMaceration_BiozymeS : DefleshingMethod
  | EnzymaticMaceration_Trypsin : DefleshingMethod
  | DermestidBeetles_Dermestes_Maculatus : DefleshingMethod
  | ChemicalSodiumHydroxide : DefleshingMethod
  | ChemicalPotassiumHydroxide : DefleshingMethod
  | ChemicalSodiumCarbonate : DefleshingMethod
  | ManualScalpelDissection : DefleshingMethod
  | ManualScraperDissection : DefleshingMethod
  | SimmeringNotBoiling : DefleshingMethod.

(* Skull regions inspected for tissue remnants *)

Inductive SkullRegion : Type :=
  | Region_Calvarium_External : SkullRegion
  | Region_Calvarium_Internal : SkullRegion
  | Region_Temporal_Fossa_Left : SkullRegion
  | Region_Temporal_Fossa_Right : SkullRegion
  | Region_Infratemporal_Fossa_Left : SkullRegion
  | Region_Infratemporal_Fossa_Right : SkullRegion
  | Region_Orbit_Left : SkullRegion
  | Region_Orbit_Right : SkullRegion
  | Region_Nasal_Cavity : SkullRegion
  | Region_Hard_Palate : SkullRegion
  | Region_Maxillary_Alveolar_Ridge : SkullRegion
  | Region_Mandibular_Alveolar_Ridge : SkullRegion
  | Region_Mandibular_Ramus_Left : SkullRegion
  | Region_Mandibular_Ramus_Right : SkullRegion
  | Region_Mandibular_Body : SkullRegion
  | Region_Zygomatic_Arch_Left : SkullRegion
  | Region_Zygomatic_Arch_Right : SkullRegion
  | Region_Mastoid_Left : SkullRegion
  | Region_Mastoid_Right : SkullRegion
  | Region_Occipital_External : SkullRegion
  | Region_Occipital_Internal : SkullRegion
  | Region_Anterior_Cranial_Fossa : SkullRegion
  | Region_Middle_Cranial_Fossa_Left : SkullRegion
  | Region_Middle_Cranial_Fossa_Right : SkullRegion
  | Region_Posterior_Cranial_Fossa : SkullRegion
  | Region_Sella_Turcica : SkullRegion
  | Region_Clivus : SkullRegion
  | Region_Petrous_Temporal_Left : SkullRegion
  | Region_Petrous_Temporal_Right : SkullRegion
  | Region_Sphenoid_Body : SkullRegion
  | Region_Greater_Wing_Left : SkullRegion
  | Region_Greater_Wing_Right : SkullRegion
  | Region_Pterygoid_Plates_Left : SkullRegion
  | Region_Pterygoid_Plates_Right : SkullRegion
  | Region_Ethmoid_Cribriform : SkullRegion
  | Region_Ethmoid_Perpendicular_Plate : SkullRegion
  | Region_Foramen_Magnum_Rim : SkullRegion
  | Region_Styloid_Process_Left : SkullRegion
  | Region_Styloid_Process_Right : SkullRegion
  | Region_Tooth_Sockets : SkullRegion.

Inductive TissueType : Type :=
  | Tissue_Muscle : CranialHarvest.CranialMuscle -> TissueType
  | Tissue_Fascia : SkullRegion -> TissueType
  | Tissue_Periosteum : SkullRegion -> TissueType
  | Tissue_Tendon : CranialHarvest.CranialMuscle -> TissueType
  | Tissue_Ligament : SkullRegion -> TissueType
  | Tissue_Cartilage : SkullRegion -> TissueType
  | Tissue_Mucosa : SkullRegion -> TissueType
  | Tissue_Fat : SkullRegion -> TissueType
  | Tissue_Glandular : SkullRegion -> TissueType
  | Tissue_Vascular : CranialHarvest.CranialVessel -> TissueType
  | Tissue_Neural : CranialHarvest.CranialNerve -> TissueType
  | Tissue_Dura : SkullRegion -> TissueType
  | Tissue_Dental_Pulp : TissueType
  | Tissue_Periodontal_Ligament : TissueType.

Record DefleshingParameters : Type := MkDefleshingParams {
  primary_method : DefleshingMethod;
  secondary_method : option DefleshingMethod;
  tertiary_method : option DefleshingMethod;
  water_temperature_c_x10 : nat;
  solution_concentration_percent_x10 : nat;
  total_duration_hours : nat;
  agitation_applied : bool;
  agitation_type : nat;
  water_changes_count : nat;
  beetle_colony_size : nat;
  beetle_enclosure_temperature_c_x10 : nat;
  manual_sessions_count : nat;
  manual_minutes_per_session : nat
}.

Record RegionInspection : Type := MkRegionInspection {
  region : SkullRegion;
  tissue_free : bool;
  periosteum_removed : bool;
  ligament_remnants : bool;
  cartilage_remnants : bool;
  grease_visible : bool;
  discoloration : bool
}.

Record DefleshingResult : Type := MkDefleshingResult {
  region_inspections : list RegionInspection;
  residual_tissue_sites : list SkullRegion;
  bone_surface_scratches : nat;
  bone_surface_gouges : nat;
  chemical_erosion_sites : nat;
  heat_damage_sites : nat;
  sutures_separated : list CranialHarvest.CranialSuture;
  teeth_lost_during_process : nat;
  nasal_conchae_intact : bool;
  nasal_septum_bony_intact : bool;
  zygomatic_arches_intact : bool;
  styloid_processes_intact : bool;
  pterygoid_plates_intact : bool;
  cribriform_plate_intact : bool;
  orbital_walls_intact : bool;
  hyoid_separated : bool;
  total_process_hours : nat
}.

Definition all_regions_count : nat := 40.

Definition regions_inspected (r : DefleshingResult) : nat :=
  length (region_inspections r).

Definition all_regions_inspected (r : DefleshingResult) : bool :=
  all_regions_count <=? regions_inspected r.

Definition no_residual_tissue (r : DefleshingResult) : bool :=
  negb (1 <=? length (residual_tissue_sites r)).

Definition no_surface_damage (r : DefleshingResult) : bool :=
  negb (1 <=? bone_surface_gouges r) &&
  (bone_surface_scratches r <=? 3) &&
  negb (1 <=? chemical_erosion_sites r) &&
  negb (1 <=? heat_damage_sites r).

Definition no_suture_separation (r : DefleshingResult) : bool :=
  negb (1 <=? length (sutures_separated r)).

Definition water_maceration_temp_valid (p : DefleshingParameters) : bool :=
  match primary_method p with
  | WaterMaceration | SimmeringNotBoiling =>
      (300 <=? water_temperature_c_x10 p) && (water_temperature_c_x10 p <=? 600)
  | _ => true
  end.

Definition chemical_concentration_valid (p : DefleshingParameters) : bool :=
  match primary_method p with
  | ChemicalSodiumHydroxide | ChemicalPotassiumHydroxide =>
      (10 <=? solution_concentration_percent_x10 p) &&
      (solution_concentration_percent_x10 p <=? 50)
  | ChemicalSodiumCarbonate =>
      (20 <=? solution_concentration_percent_x10 p) &&
      (solution_concentration_percent_x10 p <=? 100)
  | _ => true
  end.

Definition beetle_colony_valid (p : DefleshingParameters) : bool :=
  match primary_method p with
  | DermestidBeetles_Dermestes_Maculatus =>
      (500 <=? beetle_colony_size p) &&
      (250 <=? beetle_enclosure_temperature_c_x10 p) &&
      (beetle_enclosure_temperature_c_x10 p <=? 300)
  | _ => true
  end.

Definition parameters_valid (p : DefleshingParameters) : bool :=
  water_maceration_temp_valid p &&
  chemical_concentration_valid p &&
  beetle_colony_valid p &&
  (1 <=? total_duration_hours p).

Definition fragile_structures_intact (r : DefleshingResult) : bool :=
  nasal_conchae_intact r &&
  nasal_septum_bony_intact r &&
  zygomatic_arches_intact r &&
  styloid_processes_intact r &&
  pterygoid_plates_intact r &&
  cribriform_plate_intact r &&
  orbital_walls_intact r.

Definition defleshing_successful (p : DefleshingParameters)
    (r : DefleshingResult) : bool :=
  parameters_valid p &&
  all_regions_inspected r &&
  no_residual_tissue r &&
  no_surface_damage r &&
  no_suture_separation r &&
  fragile_structures_intact r &&
  (teeth_lost_during_process r <=? 2).

Lemma successful_no_residual_tissue : forall p r,
  defleshing_successful p r = true -> length (residual_tissue_sites r) = 0.
Proof.
  intros p r H. unfold defleshing_successful in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  unfold no_residual_tissue in *.
  destruct (residual_tissue_sites r) as [|x xs]; [reflexivity|].
  simpl in *. discriminate.
Qed.

Lemma successful_no_gouges : forall p r,
  defleshing_successful p r = true -> bone_surface_gouges r = 0.
Proof.
  intros p r H. unfold defleshing_successful in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  unfold no_surface_damage in *.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  destruct (bone_surface_gouges r); [reflexivity | simpl in *; discriminate].
Qed.

Lemma successful_sutures_intact : forall p r,
  defleshing_successful p r = true -> length (sutures_separated r) = 0.
Proof.
  intros p r H. unfold defleshing_successful in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  unfold no_suture_separation in *.
  destruct (sutures_separated r) as [|x xs]; [reflexivity|].
  simpl in *. discriminate.
Qed.

Lemma fragile_elim : forall r,
  fragile_structures_intact r = true ->
  nasal_conchae_intact r = true /\
  nasal_septum_bony_intact r = true /\
  zygomatic_arches_intact r = true /\
  styloid_processes_intact r = true /\
  pterygoid_plates_intact r = true /\
  cribriform_plate_intact r = true /\
  orbital_walls_intact r = true.
Proof.
  intros r H. unfold fragile_structures_intact in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  repeat split; assumption.
Qed.

Lemma defleshing_elim : forall p r,
  defleshing_successful p r = true ->
  parameters_valid p = true /\
  all_regions_inspected r = true /\
  no_residual_tissue r = true /\
  no_surface_damage r = true /\
  no_suture_separation r = true /\
  fragile_structures_intact r = true /\
  teeth_lost_during_process r <= 2.
Proof.
  intros p r H. unfold defleshing_successful in H.
  apply andb_true_iff in H. destruct H as [H Hteeth].
  apply andb_true_iff in H. destruct H as [H Hfrag].
  apply andb_true_iff in H. destruct H as [H Hnosut].
  apply andb_true_iff in H. destruct H as [H Hnodmg].
  apply andb_true_iff in H. destruct H as [H Hnores].
  apply andb_true_iff in H. destruct H as [Hpar Hreg].
  repeat split; try assumption.
  apply Nat.leb_le. exact Hteeth.
Qed.

Lemma successful_zygomatic_intact : forall p r,
  defleshing_successful p r = true -> zygomatic_arches_intact r = true.
Proof.
  intros p r H. apply defleshing_elim in H.
  destruct H as [_ [_ [_ [_ [_ [Hf _]]]]]].
  apply fragile_elim in Hf.
  destruct Hf as [_ [_ [H _]]]. exact H.
Qed.

Lemma successful_cribriform_intact : forall p r,
  defleshing_successful p r = true -> cribriform_plate_intact r = true.
Proof.
  intros p r H. apply defleshing_elim in H.
  destruct H as [_ [_ [_ [_ [_ [Hf _]]]]]].
  apply fragile_elim in Hf.
  destruct Hf as [_ [_ [_ [_ [_ [H _]]]]]]. exact H.
Qed.

Lemma beetle_temp_range : forall p r,
  primary_method p = DermestidBeetles_Dermestes_Maculatus ->
  defleshing_successful p r = true ->
  250 <= beetle_enclosure_temperature_c_x10 p /\
  beetle_enclosure_temperature_c_x10 p <= 300.
Proof.
  intros p r Hm H. apply defleshing_elim in H.
  destruct H as [Hp _].
  unfold parameters_valid in Hp.
  apply andb_true_iff in Hp. destruct Hp as [Hp _].
  apply andb_true_iff in Hp. destruct Hp as [_ Hb].
  unfold beetle_colony_valid in Hb.
  rewrite Hm in Hb.
  apply andb_true_iff in Hb. destruct Hb as [Hb Hhi].
  apply andb_true_iff in Hb. destruct Hb as [_ Hlo].
  split; apply Nat.leb_le; assumption.
Qed.

End Defleshing.

Module Degreasing.

Inductive DegreasingAgent : Type :=
  | Acetone : DegreasingAgent
  | AmmoniaHydroxide : DegreasingAgent
  | DishSoapDilute : DegreasingAgent
  | Naphtha : DegreasingAgent.

Inductive WhiteningAgent : Type :=
  | HydrogenPeroxide3 : WhiteningAgent
  | HydrogenPeroxide12 : WhiteningAgent
  | HydrogenPeroxide35 : WhiteningAgent.

Record DegreasingParameters : Type := MkDegreasingParams {
  degreasing_agent : DegreasingAgent;
  degreasing_bath_count : nat;
  degreasing_hours_per_bath : nat;
  degreasing_temperature_c_x10 : nat;
  solution_refreshed_between_baths : bool
}.

Record WhiteningParameters : Type := MkWhiteningParams {
  whitening_agent : WhiteningAgent;
  whitening_concentration_percent_x10 : nat;
  whitening_duration_hours : nat;
  whitening_wrapped : bool;
  whitening_monitored_interval_hours : nat
}.

Record DegreasingResult : Type := MkDegreasingResult {
  grease_spots_remaining : nat;
  discoloration_areas : nat;
  bone_blanched : bool;
  surface_chalky : bool;
  translucent_areas : nat;
  acetone_residue_cleared : bool;
  peroxide_neutralized : bool;
  final_ph_x10 : nat
}.

Definition degreasing_params_valid (p : DegreasingParameters) : bool :=
  (1 <=? degreasing_bath_count p) &&
  (12 <=? degreasing_hours_per_bath p) &&
  solution_refreshed_between_baths p.

Definition whitening_safe (w : WhiteningParameters) : bool :=
  match whitening_agent w with
  | HydrogenPeroxide3 => true
  | HydrogenPeroxide12 =>
      (whitening_duration_hours w <=? 24) &&
      (4 <=? whitening_monitored_interval_hours w) &&
      whitening_wrapped w
  | HydrogenPeroxide35 =>
      (whitening_duration_hours w <=? 6) &&
      (1 <=? whitening_monitored_interval_hours w) &&
      whitening_wrapped w
  end.

Definition degreasing_successful (r : DegreasingResult) : bool :=
  negb (1 <=? grease_spots_remaining r) &&
  negb (bone_blanched r) &&
  negb (surface_chalky r) &&
  negb (1 <=? translucent_areas r) &&
  acetone_residue_cleared r &&
  peroxide_neutralized r &&
  (65 <=? final_ph_x10 r) &&
  (final_ph_x10 r <=? 75).

Lemma successful_no_grease : forall r,
  degreasing_successful r = true -> grease_spots_remaining r = 0.
Proof.
  intros r H. unfold degreasing_successful in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  destruct (grease_spots_remaining r) eqn:E; [reflexivity | simpl in H; discriminate].
Qed.

Lemma successful_not_blanched : forall r,
  degreasing_successful r = true -> bone_blanched r = false.
Proof.
  intros r H. unfold degreasing_successful in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  destruct (bone_blanched r); simpl in *; [discriminate | reflexivity].
Qed.

Lemma high_concentration_requires_monitoring : forall w,
  whitening_agent w = HydrogenPeroxide35 ->
  whitening_safe w = true ->
  whitening_duration_hours w <= 6.
Proof.
  intros w Hagent H. unfold whitening_safe in H. rewrite Hagent in H.
  apply andb_true_iff in H. destruct H as [H _].
  apply andb_true_iff in H. destruct H as [H _].
  apply Nat.leb_le in H. exact H.
Qed.

End Degreasing.

Module CavityPreparation.

(* After defleshing and degreasing, the interior cranial cavity and
   facial cavities must be prepared for electronics mounting.
   This involves: clearing foramina for cable routing, drilling
   mounting points, thinning walls for weight reduction, reinforcing
   fragile areas, and creating flat mounting surfaces. *)

Inductive CavityPrepTool : Type :=
  | RotaryTool_Dremel : CavityPrepTool
  | DiamondBurr_Round_1mm : CavityPrepTool
  | DiamondBurr_Round_2mm : CavityPrepTool
  | DiamondBurr_Round_4mm : CavityPrepTool
  | DiamondBurr_Cylinder_2mm : CavityPrepTool
  | DiamondBurr_Cylinder_4mm : CavityPrepTool
  | DiamondBurr_Taper : CavityPrepTool
  | CarbideBurr_Crosscut : CavityPrepTool
  | CarbideBurr_Flame : CavityPrepTool
  | MicroDrill_05mm : CavityPrepTool
  | MicroDrill_1mm : CavityPrepTool
  | MicroDrill_15mm : CavityPrepTool
  | MicroDrill_2mm : CavityPrepTool
  | MicroDrill_3mm : CavityPrepTool
  | FlexShaft : CavityPrepTool
  | DepthGauge : CavityPrepTool
  | Calipers_Digital : CavityPrepTool
  | UltrasonicCleaner : CavityPrepTool
  | CompressedAir : CavityPrepTool
  | EndoscopeInspection : CavityPrepTool.

(* Foramen preparation status *)

Inductive ForamenPrepStatus : Type :=
  | Foramen_Unmodified : ForamenPrepStatus
  | Foramen_Cleared : ForamenPrepStatus
  | Foramen_Enlarged : ForamenPrepStatus
  | Foramen_Threaded : ForamenPrepStatus
  | Foramen_Sealed : ForamenPrepStatus
  | Foramen_Damaged : ForamenPrepStatus.

Record ForamenPrep : Type := MkForamenPrep {
  fp_foramen : CranialHarvest.Foramen;
  fp_status : ForamenPrepStatus;
  fp_diameter_mm_x10 : nat;
  fp_cable_routed : bool;
  fp_grommet_installed : bool
}.

(* Mounting point types *)

Inductive MountPointType : Type :=
  | Mount_Adhesive_Epoxy : MountPointType
  | Mount_Adhesive_Cyanoacrylate : MountPointType
  | Mount_TappedHole : MountPointType
  | Mount_PressIn_Insert : MountPointType
  | Mount_ClipRetainer : MountPointType
  | Mount_MagneticInset : MountPointType.

Inductive MountLocation : Type :=
  | Mount_Anterior_Cranial_Fossa_Floor : MountLocation
  | Mount_Middle_Cranial_Fossa_Floor_Left : MountLocation
  | Mount_Middle_Cranial_Fossa_Floor_Right : MountLocation
  | Mount_Posterior_Cranial_Fossa_Floor : MountLocation
  | Mount_Frontal_Internal_Surface : MountLocation
  | Mount_Parietal_Internal_Left : MountLocation
  | Mount_Parietal_Internal_Right : MountLocation
  | Mount_Occipital_Internal : MountLocation
  | Mount_Temporal_Internal_Left : MountLocation
  | Mount_Temporal_Internal_Right : MountLocation
  | Mount_Sphenoid_Body : MountLocation
  | Mount_Sella_Turcica : MountLocation
  | Mount_Orbit_Medial_Wall_Left : MountLocation
  | Mount_Orbit_Medial_Wall_Right : MountLocation
  | Mount_Orbit_Floor_Left : MountLocation
  | Mount_Orbit_Floor_Right : MountLocation
  | Mount_Orbit_Lateral_Wall_Left : MountLocation
  | Mount_Orbit_Lateral_Wall_Right : MountLocation
  | Mount_Orbit_Roof_Left : MountLocation
  | Mount_Orbit_Roof_Right : MountLocation
  | Mount_Nasal_Cavity_Floor : MountLocation
  | Mount_Hard_Palate_Superior : MountLocation
  | Mount_Mandible_Internal_Left : MountLocation
  | Mount_Mandible_Internal_Right : MountLocation
  | Mount_Mandible_Symphysis : MountLocation
  | Mount_Foramen_Magnum_Rim_Anterior : MountLocation
  | Mount_Foramen_Magnum_Rim_Posterior : MountLocation
  | Mount_Foramen_Magnum_Rim_Left : MountLocation
  | Mount_Foramen_Magnum_Rim_Right : MountLocation
  | Mount_Mastoid_External_Left : MountLocation
  | Mount_Mastoid_External_Right : MountLocation
  | Mount_Occipital_External_Protuberance : MountLocation.

Record MountPoint : Type := MkMountPoint {
  mp_location : MountLocation;
  mp_type : MountPointType;
  mp_depth_mm_x10 : nat;
  mp_bone_thickness_at_site_mm_x10 : nat;
  mp_load_capacity_grams : nat;
  mp_installed_successfully : bool;
  mp_bone_cracked : bool
}.

(* Wall thinning for weight reduction *)

Inductive ThinningRegion : Type :=
  | Thin_Frontal_Squama : ThinningRegion
  | Thin_Parietal_Left : ThinningRegion
  | Thin_Parietal_Right : ThinningRegion
  | Thin_Occipital_Squama : ThinningRegion
  | Thin_Temporal_Squama_Left : ThinningRegion
  | Thin_Temporal_Squama_Right : ThinningRegion.

Record ThinningOperation : Type := MkThinningOp {
  thin_region : ThinningRegion;
  thin_original_thickness_mm_x10 : nat;
  thin_final_thickness_mm_x10 : nat;
  thin_area_cm2 : nat;
  thin_perforated : bool;
  thin_inner_table_preserved : bool
}.

(* Reinforcement of fragile areas *)

Inductive ReinforcementMethod : Type :=
  | Reinforce_CyanoacrylateInfiltration : ReinforcementMethod
  | Reinforce_EpoxyCoating : ReinforcementMethod
  | Reinforce_CarbonFiberPatch : ReinforcementMethod
  | Reinforce_TitaniumMicroplate : ReinforcementMethod
  | Reinforce_BoneWax : ReinforcementMethod.

Inductive ReinforcementSite : Type :=
  | Reinforce_Orbital_Roof_Left : ReinforcementSite
  | Reinforce_Orbital_Roof_Right : ReinforcementSite
  | Reinforce_Cribriform_Plate : ReinforcementSite
  | Reinforce_Pterion_Left : ReinforcementSite
  | Reinforce_Pterion_Right : ReinforcementSite
  | Reinforce_Temporal_Squama_Left : ReinforcementSite
  | Reinforce_Temporal_Squama_Right : ReinforcementSite
  | Reinforce_Zygomatic_Arch_Left : ReinforcementSite
  | Reinforce_Zygomatic_Arch_Right : ReinforcementSite
  | Reinforce_Nasal_Bones : ReinforcementSite
  | Reinforce_Styloid_Left : ReinforcementSite
  | Reinforce_Styloid_Right : ReinforcementSite
  | Reinforce_ForamenMagnum_Rim : ReinforcementSite.

Record ReinforcementOp : Type := MkReinforcementOp {
  ro_site : ReinforcementSite;
  ro_method : ReinforcementMethod;
  ro_cured : bool;
  ro_bond_strength_tested : bool;
  ro_weight_added_grams_x10 : nat
}.

(* Overall cavity preparation record *)

Record CavityPrepResult : Type := MkCavityPrepResult {
  foramina_prepared : list ForamenPrep;
  mount_points_installed : list MountPoint;
  thinning_operations : list ThinningOperation;
  reinforcements_applied : list ReinforcementOp;
  tools_used : list CavityPrepTool;
  interior_cleaned_post_prep : bool;
  interior_inspected_endoscope : bool;
  total_weight_removed_grams_x10 : nat;
  total_weight_added_grams_x10 : nat;
  cavity_volume_cm3 : nat;
  prep_duration_hours : nat
}.

(* Critical foramina that must be cleared for cable routing *)
Definition critical_foramina_count : nat := 8.

Definition critical_foramina_cleared (r : CavityPrepResult) : bool :=
  critical_foramina_count <=? length (foramina_prepared r).

Definition minimum_mount_points : nat := 6.

Definition sufficient_mounts (r : CavityPrepResult) : bool :=
  minimum_mount_points <=? length (mount_points_installed r).

Definition no_mount_cracks (r : CavityPrepResult) : bool :=
  forallb (fun mp => negb (mp_bone_cracked mp)) (mount_points_installed r).

Definition no_thinning_perforations (r : CavityPrepResult) : bool :=
  forallb (fun t => negb (thin_perforated t)) (thinning_operations r).

Definition minimum_thinning_safe (r : CavityPrepResult) : bool :=
  forallb (fun t => 15 <=? thin_final_thickness_mm_x10 t) (thinning_operations r).

Definition all_reinforcements_cured (r : CavityPrepResult) : bool :=
  forallb (fun ro => ro_cured ro) (reinforcements_applied r).

Definition all_reinforcements_tested (r : CavityPrepResult) : bool :=
  forallb (fun ro => ro_bond_strength_tested ro) (reinforcements_applied r).

Definition minimum_cavity_volume : nat := 900.

Definition adequate_cavity_volume (r : CavityPrepResult) : bool :=
  minimum_cavity_volume <=? cavity_volume_cm3 r.

Definition cavity_prep_successful (r : CavityPrepResult) : bool :=
  critical_foramina_cleared r &&
  sufficient_mounts r &&
  no_mount_cracks r &&
  no_thinning_perforations r &&
  minimum_thinning_safe r &&
  all_reinforcements_cured r &&
  all_reinforcements_tested r &&
  adequate_cavity_volume r &&
  interior_cleaned_post_prep r &&
  interior_inspected_endoscope r.

Lemma cavity_prep_elim : forall r,
  cavity_prep_successful r = true ->
  critical_foramina_cleared r = true /\
  sufficient_mounts r = true /\
  no_mount_cracks r = true /\
  no_thinning_perforations r = true /\
  minimum_thinning_safe r = true /\
  all_reinforcements_cured r = true /\
  all_reinforcements_tested r = true /\
  adequate_cavity_volume r = true /\
  interior_cleaned_post_prep r = true /\
  interior_inspected_endoscope r = true.
Proof.
  intros r H. unfold cavity_prep_successful in H.
  apply andb_true_iff in H. destruct H as [H H9].
  apply andb_true_iff in H. destruct H as [H H8].
  apply andb_true_iff in H. destruct H as [H H7].
  apply andb_true_iff in H. destruct H as [H H6].
  apply andb_true_iff in H. destruct H as [H H5].
  apply andb_true_iff in H. destruct H as [H H4].
  apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H H2].
  apply andb_true_iff in H. destruct H as [H1 H0].
  repeat split; assumption.
Qed.

Lemma prep_requires_foramina : forall r,
  cavity_prep_successful r = true -> 8 <= length (foramina_prepared r).
Proof.
  intros r H. apply cavity_prep_elim in H.
  destruct H as [Hf _]. unfold critical_foramina_cleared in Hf.
  apply Nat.leb_le in Hf. exact Hf.
Qed.

Lemma prep_requires_mount_points : forall r,
  cavity_prep_successful r = true -> 6 <= length (mount_points_installed r).
Proof.
  intros r H. apply cavity_prep_elim in H.
  destruct H as [_ [Hm _]]. unfold sufficient_mounts in Hm.
  apply Nat.leb_le in Hm. exact Hm.
Qed.

Lemma prep_requires_900_cm3 : forall r,
  cavity_prep_successful r = true -> 900 <= cavity_volume_cm3 r.
Proof.
  intros r H. apply cavity_prep_elim in H.
  destruct H as [_ [_ [_ [_ [_ [_ [_ [Hv _]]]]]]]].
  unfold adequate_cavity_volume in Hv.
  apply Nat.leb_le in Hv. exact Hv.
Qed.

End CavityPreparation.
