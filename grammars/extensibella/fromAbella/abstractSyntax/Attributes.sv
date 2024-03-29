grammar extensibella:fromAbella:abstractSyntax;

imports extensibella:common:abstractSyntax;

imports silver:langutil:pp;
imports silver:langutil only pp, pps;

--translation to show results to user
synthesized attribute fromAbella<a>::a;


--The proof state of a full display
synthesized attribute proof::ProofState;

--Gathering hypotheses in the current proof
synthesized attribute hypList::[(String, Metaterm)];

--Whether an error occurred
synthesized attribute isError::Boolean;
--Whether a warning occurred
synthesized attribute isWarning::Boolean;

--Whether an open proof was ended (completed or aborted)
synthesized attribute proofEnded::Boolean;

