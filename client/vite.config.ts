import tailwindcss from '@tailwindcss/vite'
import react from '@vitejs/plugin-react'
import { defineConfig } from 'vite'
const clientPort = process.env.CLIENT_PORT || 3000
const serverPort = process.env.PORT || 8000

// https://vite.dev/config/
export default defineConfig({
  plugins: [react(), tailwindcss()],
  server: {
    host: true,
    port: Number(clientPort),
    proxy: {
      '/api': { target: `http://localhost:${serverPort}` },
      '/stats': { target: `http://localhost:${serverPort}` },
    },
  },
})
