#!/bin/bash
./scripts/generate_proofs.sh clear ./sample/fails
./scripts/generate_proofs.sh ./sample/fails
./scripts/filter_unknowns.sh ./sample/fails
./scripts/check_folder.sh ./sample/fails
