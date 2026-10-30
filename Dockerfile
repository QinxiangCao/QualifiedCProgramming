# Use official Coq 8.20.1 image
FROM coqorg/coq:8.20.1-ocaml-4.13.1-flambda

# Set working directory
WORKDIR /home/coq/qcp

# Copy project files and adjust permissions
COPY . /home/coq/qcp
USER root
RUN chown -R coq:coq /home/coq/qcp && chmod -R u+w /home/coq/qcp && chmod +x /home/coq/qcp/bin/linux/*
USER coq

# Build Rocq Library
ARG MAKE_JOBS=5
RUN make -C Rocq -j${MAKE_JOBS} core

# Default command (open shell)
CMD ["/bin/bash"]
