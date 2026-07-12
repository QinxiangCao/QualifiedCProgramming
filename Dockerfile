# Use official Coq 8.20.1 image
FROM coqorg/coq:8.20.1-ocaml-4.13.1-flambda

# Set working directory
WORKDIR /home/coq/qcp

# Copy project files and adjust permissions
COPY . /home/coq/qcp
USER root
RUN chown -R coq:coq /home/coq/qcp && chmod -R u+w /home/coq/qcp && chmod +x /home/coq/qcp/linux-binary/*
USER coq

# Set up CONFIGURE files
RUN echo -e "COQBIN=\nSUF=" > /home/coq/qcp/SeparationLogic/CONFIGURE && \
    echo -e "COQBIN=\nSUF=" > /home/coq/qcp/SeparationLogic/unifysl/CONFIGURE

# Build SeparationLogic Library
ARG MAKE_JOBS=5
RUN cd /home/coq/qcp/SeparationLogic/unifysl && make depend && make -j${MAKE_JOBS} && \
    cd .. && make depend && make -j${MAKE_JOBS} && make _CoqProject

# Default command (open shell)
CMD ["/bin/bash"]
