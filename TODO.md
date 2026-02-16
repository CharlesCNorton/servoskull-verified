# Servo Skull Conversion Protocol — Remaining Formalization

## Propulsion

### PropulsionUnit module
- Inductive DuctedFanType: axial ducted, centrifugal ducted, coaxial contra-rotating, solid-state ionic thruster, piezoelectric micro-thruster
- Inductive AcousticTreatment: foam-lined shroud, resonance-tuned duct, active noise cancellation transducer, labyrinth seal, none
- Inductive MotorType: brushless outrunner, brushless inrunner, coreless brushless, pancake motor
- Inductive ESCProtocol: PWM, DShot150, DShot300, DShot600, BLHeli_32, KISS
- Record FanUnit: fan_type, motor_type, esc_protocol, bell_diameter_mm, duct_inner_diameter_mm, duct_length_mm, blade_count, blade_pitch_degrees_x10, max_rpm, max_thrust_grams, weight_grams_x10, operating_voltage_x10, max_current_mA, acoustic_treatment, noise_at_hover_dB_x10, noise_at_max_dB_x10, mtbf_hours
- Record PropulsionLayout: fan_units (list FanUnit), total_fan_count, layout_symmetry_verified, center_of_thrust_offset_mm_x10, mount_locations (list CavityPreparation.MountLocation), vibration_isolation_type, vibration_damping_db_x10

### PropulsionPerformance module
- Record ThrustBudget: total_static_thrust_grams, skull_dry_weight_grams_x10, electronics_weight_grams_x10, battery_weight_grams_x10, sensor_weight_grams_x10, propulsion_weight_grams_x10, reinforcement_weight_grams_x10, cabling_weight_grams_x10, total_all_up_weight_grams_x10, thrust_to_weight_ratio_x100
- Definition minimum_thrust_to_weight_ratio: 150 (i.e., 1.5:1 for controllability)
- Definition adequate_thrust: thrust_to_weight_ratio_x100 >= minimum_thrust_to_weight_ratio
- Record FlightEnvelope: max_altitude_m, max_speed_m_per_s_x10, max_climb_rate_m_per_s_x10, max_descent_rate_m_per_s_x10, max_bank_angle_degrees, max_wind_resistance_m_per_s_x10, hover_endurance_minutes, cruise_endurance_minutes, cruise_speed_m_per_s_x10
- Definition endurance_adequate: hover_endurance_minutes >= 10
- Record NoiseProfile: idle_dB_x10, hover_dB_x10, cruise_dB_x10, max_thrust_dB_x10, frequency_peak_hz
- Definition acceptable_noise_hover: hover_dB_x10 <= 450 (45 dB)
- Definition acceptable_noise_cruise: cruise_dB_x10 <= 500 (50 dB)

### PropulsionMount module
- Inductive PropMountLocation: base_posterior_left, base_posterior_right, base_posterior_center, base_anterior_left, base_anterior_right, base_anterior_center, mastoid_left, mastoid_right, occipital_midline, foramen_magnum_surround_left, foramen_magnum_surround_right, foramen_magnum_surround_posterior
- Record PropMountDetail: location, bone_thickness_at_mount_mm_x10, mount_type (from CavityPreparation), load_bearing_capacity_grams, vibration_isolator_installed, isolator_frequency_cutoff_hz, duct_clearance_from_bone_mm, intake_obstruction_percent, exhaust_obstruction_percent
- Definition mount_structurally_sound: bone_thickness >= 20 (2mm) and load_capacity >= max_thrust of attached fan
- Definition airflow_unobstructed: intake_obstruction_percent <= 10 and exhaust_obstruction_percent <= 10

### Lemmas
- adequate_thrust_implies_liftoff: thrust > weight -> can hover
- noise_budget_within_social_acceptability: hover noise <= 45 dB
- symmetric_layout_implies_stable_hover: if layout_symmetry_verified then center_of_thrust within tolerance
- minimum_fan_count: total_fan_count >= 4 for stability
- single_fan_failure_survivable: if total_fan_count >= 6 then losing one fan still exceeds weight (prove thrust - single_fan_max > total_weight)

---

## Power

### BatteryCell module
- Inductive CellChemistry: lithium_polymer, lithium_ion_NMC, lithium_ion_LFP, solid_state_lithium, lithium_sulfur, sodium_ion
- Record CellSpec: chemistry, nominal_voltage_mV, capacity_mAh, max_discharge_rate_C, weight_grams_x10, volume_mm3, cycle_life, operating_temp_min_c_x10, operating_temp_max_c_x10, internal_resistance_mOhm
- Record BatteryPack: cells (list CellSpec), series_count, parallel_count, pack_voltage_mV, pack_capacity_mAh, pack_weight_grams_x10, pack_volume_mm3, bms_present, bms_cell_balancing, over_discharge_protection, over_charge_protection, thermal_monitoring, thermal_cutoff_c_x10

### PowerBudget module
- Record Subsystem: name (nat encoding), peak_draw_mA, typical_draw_mA, standby_draw_mA, voltage_mV
- Inductive PowerState: dormant, idle, hover, cruise, max_thrust, compute_heavy, transmit_burst
- Record PowerBudgetAtState: state, total_draw_mA, battery_voltage_under_load_mV, estimated_endurance_minutes
- Definition power_budget: for each PowerState, sum subsystem draws, compare to battery capacity
- Definition endurance_at_hover: (pack_capacity_mAh * 60) / hover_total_draw_mA
- Definition endurance_at_cruise: (pack_capacity_mAh * 60) / cruise_total_draw_mA

### ChargingSystem module
- Inductive ChargingMethod: inductive_wireless, USB_C_PD, pogo_pin_contact, solar_supplemental
- Record ChargingSpec: method, max_charge_rate_mA, charge_voltage_mV, charge_time_to_80_percent_minutes, charge_time_to_full_minutes, dock_alignment_tolerance_mm, coil_diameter_mm (for wireless)
- Record ChargingDock: charging_spec, dock_weight_grams, dock_cradle_shape_matches_skull, skull_resting_stable, continuous_power_available

### Lemmas
- battery_fits_in_cavity: pack_volume_mm3 <= cavity_volume_cm3 * 1000
- endurance_meets_minimum: endurance_at_hover >= 10 minutes
- charge_rate_safe: max_charge_rate_C <= 1C for longevity
- bms_required: bms_present = true for any pack with series_count >= 2
- thermal_operating_range: operating range covers expected ambient (0-40C)
- no_over_discharge: over_discharge_protection = true
- dock_cradle_fit: dock_cradle_shape_matches_skull = true

---

## Sensors

### VisualSensors module
- Inductive CameraType: RGB, RGB_IR, depth_structured_light, depth_ToF, thermal_LWIR, thermal_MWIR, event_camera_DVS
- Record CameraSpec: camera_type, resolution_h, resolution_v, framerate, fov_h_degrees_x10, fov_v_degrees_x10, focal_length_mm_x10, aperture_f_x10, weight_grams_x10, power_draw_mA, interface_type (nat), lens_diameter_mm_x10, sensor_diagonal_mm_x10
- Inductive CameraMountLocation: orbit_left, orbit_right, frontal_midline, occipital_midline, temporal_left, temporal_right
- Record CameraMount: camera, location, secured, aligned, calibrated, lens_flush_with_surface, cosmetic_integration_score (nat 1-10)
- Record StereoConfig: left_camera, right_camera, baseline_mm, calibrated, rectified, depth_range_min_mm, depth_range_max_mm

### AudioSensors module
- Inductive MicrophoneType: MEMS_omnidirectional, MEMS_cardioid, electret_condenser, piezoelectric_bone_conduction
- Record MicrophoneSpec: mic_type, sensitivity_dBV_x10, frequency_response_low_hz, frequency_response_high_hz, snr_dB_x10, weight_grams_x10, power_draw_uA, diameter_mm_x10
- Inductive MicMountLocation: temporal_left, temporal_right, frontal, occipital, nasal_aperture, auditory_meatus_left, auditory_meatus_right
- Record MicrophoneArray: mics (list (MicrophoneSpec * MicMountLocation)), total_mic_count, beamforming_capable, noise_cancellation_capable, spatial_resolution_degrees

### AudioOutput module
- Inductive SpeakerType: balanced_armature, micro_dynamic, bone_conduction_transducer, piezoelectric_disc
- Record SpeakerSpec: speaker_type, frequency_response_low_hz, frequency_response_high_hz, max_spl_dB_x10, impedance_ohm, power_rating_mW, weight_grams_x10, diameter_mm_x10
- Inductive SpeakerMountLocation: oral_cavity, nasal_cavity, palate_superior, mandible_body_left, mandible_body_right, mastoid_left_bone_conduction, mastoid_right_bone_conduction
- Record SpeakerConfig: speaker, location, sealed_back_volume, resonance_tuned, cosmetic_concealment

### ProximitySensors module
- Inductive ProxSensorType: ultrasonic, IR_time_of_flight, IR_triangulation, LiDAR_solid_state, LiDAR_spinning, radar_mmWave
- Record ProxSensorSpec: sensor_type, range_min_mm, range_max_mm, angular_fov_degrees_x10, update_rate_hz, accuracy_mm, weight_grams_x10, power_draw_mA
- Inductive ProxMountLocation: frontal_superior, frontal_inferior, temporal_left, temporal_right, occipital, base_inferior, vertex
- Record ProxSensorConfig: sensor, location, calibrated, obstruction_free

### EnvironmentalSensors module
- Record EnvironmentalSuite: barometer_present, barometer_altitude_resolution_cm, magnetometer_present, magnetometer_calibrated, imu_present, imu_gyro_dps, imu_accel_g, imu_update_rate_hz, temperature_sensor_present, humidity_sensor_present, ambient_light_sensor_present, gps_present, gps_accuracy_m_x10

### Lemmas
- stereo_requires_two_cameras: stereo config valid -> left and right cameras both installed
- stereo_baseline_positive: baseline_mm >= 30 for useful depth
- mic_array_beamforming_requires_three: beamforming_capable = true -> total_mic_count >= 3
- speaker_audible: max_spl_dB_x10 >= 600 (60 dB at 1m)
- obstacle_avoidance_coverage: at least 4 proximity sensors covering 360 degrees
- imu_required_for_flight: imu_present = true (hard requirement)
- barometer_required_for_altitude_hold: barometer_present = true

---

## Compute

### ProcessorBoard module
- Inductive ProcessorFamily: arm_cortex_a, arm_cortex_m, risc_v, x86_embedded, custom_asic, fpga_hybrid
- Inductive AcceleratorType: gpu_integrated, npu_dedicated, tpu_dedicated, fpga_accelerator, none
- Record ProcessorSpec: family, core_count, clock_mhz, cache_kb, ram_mb, flash_mb, tdp_mW, weight_grams_x10, dimensions_mm_l, dimensions_mm_w, dimensions_mm_h, operating_temp_min_c_x10, operating_temp_max_c_x10
- Record AcceleratorSpec: accel_type, tops_x10 (tera operations per second * 10), power_draw_mW, supported_precision (nat encoding: fp32, fp16, int8)
- Record ComputeBoard: processor, accelerator (option AcceleratorSpec), total_ram_mb, storage_gb, total_power_draw_mW, total_weight_grams_x10, total_volume_mm3, boot_time_seconds, has_hardware_watchdog, has_secure_boot, has_encrypted_storage

### ComputePerformance module
- Record InferenceCapability: max_model_parameters_millions, tokens_per_second_x10, first_token_latency_ms, context_window_tokens, concurrent_streams, model_fits_in_ram
- Record NavigationCompute: slam_fps, obstacle_detection_latency_ms, path_planning_latency_ms, sensor_fusion_latency_ms
- Record VoiceCompute: speech_recognition_rtf_x100 (real-time factor * 100, must be < 100), voice_synthesis_rtf_x100, wake_word_detection_latency_ms
- Definition inference_adequate: tokens_per_second_x10 >= 50 (5 tok/s minimum for conversational)
- Definition navigation_adequate: obstacle_detection_latency_ms <= 50
- Definition voice_adequate: speech_recognition_rtf_x100 <= 100

### ComputeMount module
- Record ComputeBoardMount: board, mount_location (CavityPreparation.MountLocation), thermal_pad_installed, heat_sink_attached, heat_sink_weight_grams_x10, airflow_path_clear, maximum_junction_temp_c_x10, fan_cooling_available, passive_cooling_sufficient

### CommunicationsModule
- Inductive RadioType: wifi_6, wifi_6e, wifi_7, bluetooth_5, bluetooth_le, cellular_5g_nr, cellular_lte, lora, mesh_protocol, uwb
- Record RadioSpec: radio_type, frequency_mhz, bandwidth_mhz, max_data_rate_kbps, range_m, tx_power_dBm_x10, rx_sensitivity_dBm_x10, antenna_type (nat), antenna_gain_dBi_x10, power_draw_active_mA, power_draw_idle_mA, weight_grams_x10
- Inductive AntennaLocation: internal_calvarium, orbit_rim_left, orbit_rim_right, mastoid_left, mastoid_right, mandible_body, foramen_magnum_surround
- Record RadioConfig: radio, antenna_location, antenna_installed, rf_path_clear, interference_tested
- Record CommsStack: radios (list RadioConfig), primary_uplink, fallback_uplink, mesh_capable, encrypted, encryption_protocol (nat), latency_to_cloud_ms

### Lemmas
- compute_board_fits: total_volume_mm3 fits within remaining cavity volume after battery
- thermal_within_limits: junction temp under load <= operating_temp_max
- inference_or_cloud: either local inference adequate or primary_uplink reliable
- watchdog_required: has_hardware_watchdog = true (safety requirement for autonomous flight)
- encrypted_comms_required: encrypted = true
- at_least_two_radios: length radios >= 2 (primary + fallback)
- secure_boot_required: has_secure_boot = true

---

## Personality Substrate

### PersonalitySubstrate module
- Record t: corpus (BehavioralCorpus.t), substrate_size_bytes, substrate_version, derivation_timestamp, fidelity_score_x1000 (0-1000), voice_fidelity_score_x1000, motor_fidelity_score_x1000, runs_on_edge, runs_on_cloud, edge_tokens_per_second_x10, cloud_tokens_per_second_x10
- Definition fidelity_threshold: 700 (0.7 on 0-1 scale)
- Definition voice_fidelity_threshold: 600
- Definition motor_fidelity_threshold: 500
- Definition fidelity_adequate: fidelity_score_x1000 >= fidelity_threshold
- Definition voice_fidelity_adequate: voice_fidelity_score_x1000 >= voice_fidelity_threshold
- Definition motor_fidelity_adequate: motor_fidelity_score_x1000 >= motor_fidelity_threshold
- Definition substrate_valid: fidelity_adequate and voice_fidelity_adequate and motor_fidelity_adequate and corpus_sufficient (corpus)
- Definition edge_capable: runs_on_edge = true and edge_tokens_per_second_x10 >= 30
- Definition cloud_capable: runs_on_cloud = true

### VoiceSynthesis module
- Record VoiceProfile: sample_rate_hz, bit_depth, speaker_embedding_dimensions, prosody_model_present, emotion_modulation_capable, languages_supported_count, mean_opinion_score_x10 (1-50)
- Definition voice_quality_adequate: mean_opinion_score_x10 >= 35 (3.5 MOS)
- Record VoiceConfig: profile, speaker_output (AudioOutput.SpeakerConfig), latency_ms, streaming_capable

### MotorBehavior module
- Record AttentionProfile: saccade_speed_degrees_per_second, smooth_pursuit_capable, default_gaze_direction, gaze_tracking_enabled, head_bob_during_hover (bool, subtle idle movement), approach_speed_m_per_s_x10, retreat_speed_m_per_s_x10, personal_space_radius_cm, following_distance_cm, altitude_preference_cm (relative to interlocutor eye level)
- Record IdleBehavior: hover_drift_amplitude_mm, hover_drift_period_seconds_x10, slight_rotation_enabled, rotation_amplitude_degrees_x10, breathing_simulation_enabled (subtle altitude oscillation)
- Definition motor_behavior_naturalistic: saccade_speed > 0 and personal_space_radius >= 30 and approach_speed > 0

### FallbackBehavior module
- Inductive FallbackLevel: full_personality, reduced_personality, navigation_only, return_to_dock, safe_landing, emergency_shutdown
- Record FallbackStack: levels (list FallbackLevel), cloud_disconnect_triggers_level, low_battery_triggers_level, sensor_failure_triggers_level, compute_fault_triggers_level
- Definition fallback_safe: return_to_dock is in the stack, emergency_shutdown is in the stack
- Definition graceful_degradation: for each trigger, the assigned level is reasonable (e.g., cloud_disconnect >= reduced_personality, not emergency_shutdown)

### Lemmas
- substrate_requires_corpus: substrate_valid -> corpus_sufficient (corpus)
- substrate_requires_fidelity: substrate_valid -> fidelity >= 0.7
- voice_requires_speaker: voice config valid -> speaker installed and audible
- motor_behavior_respects_personal_space: personal_space_radius >= 30 cm
- fallback_always_has_safe_landing: safe_landing in stack
- fallback_always_has_dock_return: return_to_dock in stack
- edge_or_cloud_available: edge_capable or cloud_capable (at least one)

---

## Commissioning

### PreCommissioningChecks module
- Record FlightReadiness: all_fans_spin_test_passed, each_fan_thrust_measured, center_of_gravity_within_tolerance, imu_calibrated, magnetometer_calibrated, barometer_calibrated, gps_lock_acquired (if applicable), motor_response_time_ms, pid_gains_tuned, hover_stability_test_passed (10 second hover), transition_test_passed (hover to cruise), emergency_stop_test_passed, failsafe_test_passed (single fan kill), battery_full, battery_voltage_within_spec, all_sensors_responding, stereo_calibration_verified, proximity_sensors_verified, temperature_within_limits
- Record CommunicationsReadiness: primary_uplink_connected, fallback_uplink_tested, latency_acceptable, bandwidth_adequate, encryption_verified, cloud_personality_endpoint_reachable (if cloud mode)
- Record SubstrateReadiness: personality_loaded, fidelity_verified_against_holdout, voice_synthesis_test_passed, voice_mos_measured, motor_behavior_calibrated, fallback_stack_loaded, consent_directives_loaded, kill_conditions_loaded, identity_disclaimer_configured
- Record PhysicalReadiness: all_mounts_secure, all_cables_routed, all_foramina_grommeted, no_loose_components, weight_measured_and_recorded, center_of_gravity_measured, cosmetic_inspection_passed, teeth_secured (if retained), mandible_articulation_tested (if retained)

### CommissioningCeremony module
- Record CommissioningRecord: subject (Subject.t), authorization_verified, pre_flight_checks_passed, communications_checks_passed, substrate_checks_passed, physical_checks_passed, first_flight_successful, first_voice_interaction_recorded, fidelity_score_at_commissioning, commissioning_authority_id, commissioning_date_unix, witnesses_present_count, commissioning_location_id
- Definition commissioning_valid: all checks passed and authorization verified and first_flight_successful
- Definition commissioned: commissioning_valid = true

### Lemmas
- commissioning_requires_authorization: commissioned -> subject is_authorized = true
- commissioning_requires_flight: commissioned -> first_flight_successful = true
- commissioning_requires_substrate: commissioned -> personality loaded and fidelity verified
- commissioning_requires_consent: commissioned -> consent_directives_loaded = true
- commissioning_requires_kill_conditions: commissioned -> kill_conditions_loaded = true
- no_commissioning_without_death: commissioned -> subject is_deceased = true
- no_commissioning_without_corpus: commissioned -> corpus_sufficient = true

---

## Lifecycle

### LifecycleState module
- Inductive State: dormant, active, degraded_grounded, degraded_voiceless, degraded_offline, maintenance, decommissioned
- Record StateTransition: from_state, to_state, trigger (nat encoding), timestamp_unix, authorized_by (option nat)
- Inductive Trigger: power_on, power_off, battery_low, battery_critical, sensor_failure, compute_fault, propulsion_failure, cloud_disconnect, cloud_reconnect, maintenance_requested, maintenance_complete, kill_condition_met, consent_revoked, manual_decommission, age_limit_reached, physical_damage_detected
- Definition valid_transition: from -> to -> trigger -> bool (encode all valid transitions)
  - dormant -> active (power_on)
  - active -> dormant (power_off)
  - active -> degraded_grounded (propulsion_failure, sensor_failure critical)
  - active -> degraded_voiceless (compute_fault partial, speaker failure)
  - active -> degraded_offline (cloud_disconnect)
  - degraded_offline -> active (cloud_reconnect)
  - degraded_grounded -> maintenance (maintenance_requested)
  - degraded_voiceless -> maintenance (maintenance_requested)
  - active -> maintenance (maintenance_requested)
  - maintenance -> active (maintenance_complete, all checks pass)
  - maintenance -> dormant (maintenance_complete, not all checks pass)
  - any -> decommissioned (kill_condition_met, consent_revoked, manual_decommission, age_limit_reached)
  - decommissioned -> nothing (terminal state, no transitions out)

### OperationalLimits module
- Record OperationalConstraints: max_flight_hours_per_day, max_continuous_flight_minutes, mandatory_rest_minutes_between_flights, max_altitude_m, max_distance_from_dock_m, no_fly_zones (list nat encoding), curfew_start_hour, curfew_end_hour, interaction_whitelist (option (list nat)), interaction_blacklist (option (list nat)), max_voice_volume_dB_x10, recording_consent_required_from_interlocutors
- Definition within_operational_limits: current state satisfies all constraints

### MaintenanceSchedule module
- Record MaintenanceItem: component_id, check_type (nat), interval_hours, last_performed_hours, overdue
- Record MaintenanceLog: items (list MaintenanceItem), total_flight_hours, total_charge_cycles, firmware_version, last_substrate_update, last_full_inspection_date_unix
- Definition maintenance_current: no items overdue

### Decommissioning module
- Inductive DecommissionReason: consent_revoked, kill_condition_met, physical_destruction, age_limit, manual_authority, legal_order
- Record DecommissionRecord: reason, timestamp_unix, authority_id, personality_wiped, storage_zeroed, hardware_powered_down, skull_disposition (nat: returned_to_estate, museum, destroyed, interred)
- Definition decommission_complete: personality_wiped and storage_zeroed and hardware_powered_down

### Lemmas
- decommissioned_is_terminal: State = decommissioned -> no valid transition to any other state
- kill_condition_forces_decommission: kill_condition_met -> next state = decommissioned
- consent_revocation_forces_decommission: consent_revoked -> next state = decommissioned
- decommission_wipes_personality: decommission_complete -> personality_wiped = true
- decommission_wipes_storage: decommission_complete -> storage_zeroed = true
- active_requires_all_checks: State = active -> all pre-flight checks were passed at some point
- degraded_cannot_fly: State = degraded_grounded -> propulsion disabled
- maintenance_reachable_from_any_non_terminal: for all non-terminal states, reachable maintenance

---

## Safety Properties (cross-cutting)

### HarvestSafety module
- alive_never_harvested: forall s, vital_status s = Alive -> eligible_for_harvest s = false
- unauthorized_never_harvested: forall s, is_authorized s = false -> eligible_for_harvest s = false
- decomposed_never_harvested: decomposition_grade > 1 -> harvest_successful = false
- structural_damage_fails_harvest: any bone damaged -> harvest_successful = false

### FlightSafety module
- cannot_fly_without_thrust: thrust <= weight -> hover impossible
- cannot_fly_without_imu: imu_present = false -> flight_readiness = false
- cannot_fly_without_battery: battery empty -> immediate safe landing
- single_point_failure_analysis: for each critical subsystem, failure leads to defined degraded state, never undefined behavior
- noise_within_social_limits: hover noise <= 45 dB, cruise noise <= 50 dB

### IdentitySafety module
- not_the_person: the formalization includes an explicit axiom or definition that the personality substrate is a behavioral approximation, not identity continuity
- fidelity_bounded: fidelity score is bounded [0, 1] and commissioning requires >= 0.7
- consent_chain_unbroken: from authorization through commissioning, consent/merit verified at every state transition
- kill_condition_irrevocable: once triggered, cannot be un-triggered
- decommission_irrevocable: once decommissioned, cannot be recommissioned

### IntegrationSafety module
- total_weight_consistent: sum of all component weights = total_all_up_weight
- cavity_volume_not_exceeded: sum of all component volumes <= cavity_volume_cm3 * 1000
- power_budget_balanced: total draw at max state <= battery discharge capacity
- thermal_budget_balanced: total heat generation <= thermal dissipation capacity
- no_component_exceeds_mount_capacity: each mounted component weight <= mount load_capacity
- all_cables_routed_through_foramina: no cable exits through bone surface (only through natural or prepared foramina)

---

## Witness Examples

### WitnessExamples module
- Construct a complete valid servo skull from authorization through commissioning
  - Subject: deceased, consent signed, 2 witnesses, not revoked
  - Corpus: 500 hours audio, 100k words text, 5 distinct sources
  - Harvest: full procedure, all 62 muscles, all 24 nerves, all 20 vessels, all 19 intracranial contents, all 12 orbital contents, all 14 nasal/oral contents, all bones intact, all foramina patent
  - Defleshing: water maceration at 35C, all 40 regions inspected, no residual tissue, no damage
  - Degreasing: acetone, 3 baths, no grease remaining, neutral pH
  - Cavity prep: 8 foramina cleared, 8 mount points, no cracks, 1000 cm3 volume
  - Propulsion: 6 ducted fans, 2:1 thrust ratio, 42 dB hover noise
  - Battery: solid-state lithium, 15 min hover endurance, BMS with all protections
  - Sensors: stereo cameras in orbits, 4 MEMS mics, balanced armature speaker, 6 ToF sensors, full environmental suite
  - Compute: ARM Cortex-A with NPU, 8 TOPS, 4GB RAM, WiFi 6 + BLE
  - Personality: fidelity 0.85, voice MOS 4.0, motor fidelity 0.7, edge capable at 8 tok/s
  - Commissioning: all checks passed, first flight successful, 2 witnesses
  - Prove: classify as commissioned, all safety properties hold

### CounterexampleWitnesses module
- alive_subject_blocked: construct alive subject, prove harvest fails
- no_consent_blocked: construct deceased subject without consent, prove harvest blocked
- decomposed_blocked: construct subject dead > 72h with decomposition grade 2, prove harvest fails
- insufficient_corpus_blocked: construct empty corpus, prove commissioning fails
- underthrust_blocked: construct system with thrust < weight, prove flight readiness fails
- no_imu_blocked: construct system without IMU, prove flight readiness fails
- low_fidelity_blocked: construct substrate with fidelity 0.5, prove commissioning fails

---

## Estimated line counts

| Module group | Estimated lines |
|---|---|
| Propulsion (3 modules) | 400-500 |
| Power (3 modules) | 300-400 |
| Sensors (5 modules) | 500-600 |
| Compute (4 modules) | 400-500 |
| Personality Substrate (4 modules) | 350-450 |
| Commissioning (2 modules) | 250-350 |
| Lifecycle (4 modules) | 400-500 |
| Safety Properties (4 modules) | 300-400 |
| Witness Examples (2 modules) | 400-500 |
| **Total remaining** | **~3500-4200** |
| **Current (committed)** | **1500** |
| **Projected total** | **~5000-5700** |
