import { TypedUseSelectorHook, useDispatch, useSelector } from 'react-redux'
import type { RootState, AppDispatch } from './state/store'

import { setMobile as setMobileState, setLockMobile as setLockMobileState} from "./state/preferences"

// Use throughout your app instead of plain `useDispatch` and `useSelector`
export const useAppDispatch: () => AppDispatch = useDispatch
export const useAppSelector: TypedUseSelectorHook<RootState> = useSelector

export const useMobile = () => {
  const dispatch = useAppDispatch();

  const mobile = useAppSelector((state) => state.preferences.mobile);
  const lockMobile = useAppSelector((state) => state.preferences.lockMobile);

  const setMobile = (val: boolean) => {
    dispatch(setMobileState(val));
  };

  const setLockMobile = (val: boolean) => {
    dispatch(setLockMobileState(val));
  };

  return {
    mobile,
    setMobile,
    lockMobile,
    setLockMobile,
  };
};
