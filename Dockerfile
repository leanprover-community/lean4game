# Multi-stage build for Lean4Game
FROM node:22-alpine AS base

# Install system dependencies
RUN apk add --no-cache \
    curl \
    bash \
    git \
    build-base \
    python3 \
    make \
    g++

# Set working directory
WORKDIR /app

# Copy package files
COPY package*.json ./
COPY tsconfig.json ./
COPY vite.config.ts ./

# Install dependencies
RUN npm install --force

# Build stage
FROM base AS builder

# Copy source code
COPY client/ ./client/
COPY relay/ ./relay/
COPY server/ ./server/
COPY index.html ./
COPY env.d.ts ./

# Install elan (Lean package manager) and build
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y && \
    export PATH="/root/.elan/bin:$PATH" && \
    npm run build:server && npm run build:relay && npm run build:client

# Production stage
FROM node:22-alpine AS production

# Create non-root user for security
RUN addgroup -g 1001 -S nodejs && \
    adduser -S lean4game -u 1001

# Install minimal runtime dependencies only
RUN apk add --no-cache curl && \
    rm -rf /var/cache/apk/*

# Set working directory
WORKDIR /app

# Copy elan from builder stage
COPY --from=builder /root/.elan /home/lean4game/.elan

# Copy built application with proper ownership
COPY --from=builder --chown=lean4game:nodejs /app/client/dist ./client/dist
COPY --from=builder --chown=lean4game:nodejs /app/relay/dist ./relay/dist
COPY --from=builder --chown=lean4game:nodejs /app/server ./server
COPY --from=builder --chown=lean4game:nodejs /app/package*.json ./

# Install only production dependencies
RUN npm ci --only=production --no-audit --no-fund && \
    npm cache clean --force && \
    rm -rf /tmp/* /var/tmp/*

# Set environment variables
ENV NODE_ENV=production
ENV PORT=8080
ENV CLIENT_PORT=3000
ENV VITE_CLIENT_DEFAULT_LANGUAGE=en
ENV PATH="/home/lean4game/.elan/bin:$PATH"

# Change ownership of the app directory
RUN chown -R lean4game:nodejs /app

# Switch to non-root user
USER lean4game

# Expose default port (can be overridden at runtime with -p flag)
EXPOSE 8080

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:8080/ || exit 1

# Start the application
CMD ["npm", "run", "production"]
