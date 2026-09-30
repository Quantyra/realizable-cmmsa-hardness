## Pre-cloud preparation failure

The attempted FB0B2B25 source capture failed its SHA assertion because the proof owner had already advanced the working file to 1D8691E8. No FB snapshot was produced. The driver invocation then exited before preparation or any cloud command with FileNotFoundError for margin-FB0B2B25.lean.snapshot (tool chunk 457c23, exit 1). This is a local preparation failure, not a Lean diagnostic or executed cloud run. The original failed tool result is in session history; this note records observed fields and does not reconstruct a raw terminal transcript.

The held 1D8691E8 bytes were then captured successfully. The subsequent actual run is cmmsa_analytic_20260930T124243Z, session 47708, with source hashes recorded in its preparation.json. The historical driver filename retains FB0B2B25; its archived executed argument data and source pins identify the actual 1D8691E8 input.
